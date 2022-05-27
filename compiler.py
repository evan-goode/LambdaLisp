#!/usr/bin/env python3

# "A language targeting SectorLambda sounds super cool." -Justine Tunney

from abc import ABC, abstractmethod
from ast import literal_eval
from dataclasses import dataclass
from subprocess import run, PIPE
from typing import Dict, FrozenSet, Generator, Iterator, List, NamedTuple, Optional, Sequence, Tuple
from uuid import uuid4
import re
import sys

# For reasoning about indirect recursion
import networkx as nx

from more_itertools import peekable

# Raise the stack limit or we hit the maximum recursion depth, maybe Python was
# a bad choice
import resource, sys
resource.setrlimit(resource.RLIMIT_STACK, (2 ** 29, -1))
sys.setrecursionlimit(10 ** 6)

# Use our build of the Blc interpreter
PATH_TO_BLC_INTERPRETER = "./lambda"


Context = Dict[str, int]

class SrcExpr(ABC):
    """An expression in the source language"""

    @abstractmethod
    def simplify(self) -> "SimpleExpr":
        """Convert to a simplified subset of the source language"""
        pass

    def to_dbn(self, context: Context) -> str:
        """Convert this expression to an equivalent expression in lambda
        calculus. The `context` parameter maps variable names to their de
        Bruijn indices"""
        return self.simplify().to_dbn(context)

class SimpleExpr(SrcExpr):
    """Intermediate, simplified subset of source language. We convert to this
    intermediate representation to figure out which variables an expression
    references. `get_references` is easy to compute in the simplified language,
    since only SrcVars can make references, but awkward in the source
    language."""
    @abstractmethod
    def to_dbn(self, context: Context) -> str:
        pass

    @abstractmethod
    def get_references(self) -> frozenset[str]:
        """Get the set of variables the expression references"""
        pass

@dataclass
class SrcAbs(SimpleExpr):
    """Abstraction with a single named variable."""
    var_name: str
    expr: SrcExpr

    def get_references(self) -> frozenset[str]:
        # Don't count references to the bound variable
        return self.expr.simplify().get_references() - frozenset((self.var_name,))

    def simplify(self) -> SimpleExpr:
        return SrcAbs(self.var_name, self.expr.simplify())

    def to_dbn(self, context: Context) -> str:
        # Increment the de Bruijn index of each variable already bound
        new_context = {k: v + 1 for k, v in context.items()}

        # and set the index of the newly-bound variable to 0
        new_context[self.var_name] = 0
        return f"λ {self.expr.to_dbn(new_context)}"

@dataclass
class SrcAnonAbs(SimpleExpr):
    """Abstraction with an unnamed variable. Used for translating de Bruijn
    lambda calculus directly into the source language."""
    expr: SrcExpr

    def get_references(self) -> frozenset[str]:
        return self.expr.simplify().get_references()

    def simplify(self) -> SimpleExpr:
        return SrcAnonAbs(self.expr.simplify())

    def to_dbn(self, context: Context) -> str:
        new_context = {k: v + 1 for k, v in context.items()}
        return f"λ {self.expr.to_dbn(new_context)}"

@dataclass
class SrcVar(SimpleExpr):
    """Named variable"""
    name: str

    def get_references(self) -> frozenset[str]:
        return frozenset((self.name,))

    def simplify(self) -> SimpleExpr:
        return self

    def to_dbn(self, context: Context) -> str:
        # Look up the variable's index in the `context`
        return str(context[self.name])

@dataclass
class SrcAnonVar(SimpleExpr):
    """Unnamed variable with only an index."""
    index: int

    def get_references(self) -> frozenset[str]:
        return frozenset()

    def simplify(self) -> SimpleExpr:
        return self

    def to_dbn(self, context: Context) -> str:
        return str(self.index)

@dataclass
class SrcApp(SimpleExpr):
    """Function application."""
    function: SrcExpr
    argument: SrcExpr

    def get_references(self) -> frozenset[str]:
        return self.function.simplify().get_references() | self.argument.simplify().get_references()

    def simplify(self) -> SimpleExpr:
        return SrcApp(self.function.simplify(), self.argument.simplify())

    def to_dbn(self, context: Context) -> str:
        return f"[{self.function.to_dbn(context)} {self.argument.to_dbn(context)}]"

def dbn_to_srcexpr(dbn: str) -> SimpleExpr:
    """Convert de Bruijn notation lambda calculus directly to the source
    language."""

    def dbn_to_srcexpr_rem(dbn: str) -> Tuple[SimpleExpr, str]:
        char = dbn[0]
        if char == "λ":
            body, remaining = dbn_to_srcexpr_rem(dbn[1:])
            return SrcAnonAbs(body), remaining
        elif char == "[":
            function, remaining = dbn_to_srcexpr_rem(dbn[1:])
            argument, remaining = dbn_to_srcexpr_rem(remaining[1:])
            return SrcApp(function, argument), remaining
        elif char in "0123456789":
            return SrcAnonVar(int(char)), dbn[1:]
        else:
            return dbn_to_srcexpr_rem(dbn[1:])

    return dbn_to_srcexpr_rem(dbn)[0]

@dataclass
class SrcCall(SrcExpr):
    """Function application with multiple arguments."""

    function: SrcExpr
    arguments: List[SrcExpr]

    def _make_call(self, arguments: List[SrcExpr]) -> SrcExpr:
        if not arguments:
            return SrcApp(self.function, SrcNil())
        if len(arguments) == 1:
            return SrcApp(self.function, arguments[0])
        return SrcApp(self._make_call(arguments[:-1]), arguments[-1])

    def simplify(self) -> SimpleExpr:
        return self._make_call(self.arguments).simplify()

@dataclass
class SrcLambda(SrcExpr):
    """Function definition with multiple arguments"""
    var_names: List[str]
    expr: SrcExpr

    def _make_lambda(self, var_names: List[str]) -> SrcExpr:
        if not var_names:
            return SrcAnonAbs(self.expr)
        if len(var_names) == 1:
            return SrcAbs(var_names[0], self.expr)
        return SrcAbs(var_names[0], self._make_lambda(var_names[1:]))

    def simplify(self) -> SimpleExpr:
        return self._make_lambda(self.var_names).simplify()

@dataclass
class SrcNat(SrcExpr):
    """Church numeral"""
    value: int

    def __post_init__(self) -> None:
        if self.value < 0:
            raise ValueError("Nat cannot be less than 0!")

    def _make_nat(self, n: int) -> SrcExpr:
        if n == 0:
            return SrcAnonVar(0)
        return SrcApp(
                SrcAnonVar(1),
                self._make_nat(n - 1)
            )

    def simplify(self) -> SimpleExpr:
        return SrcAnonAbs(SrcAnonAbs(
            self._make_nat(self.value)
        )).simplify()

@dataclass
class SrcBool(SrcExpr):
    """Boolean. λλ 0 is false, λλ 1 is true."""
    value: bool

    def simplify(self) -> SimpleExpr:
        return dbn_to_srcexpr(f"λλ {int(self.value)}")

@dataclass
class SrcNil(SrcExpr):
    """Equivalent to SrcBool(False)"""
    nil = dbn_to_srcexpr("λλ 0")

    def simplify(self) -> SimpleExpr:
        return self.nil

@dataclass
class SrcList(SrcExpr):
    """List of elements, i.e. (pair a (pair b (pair c ...)))"""
    elements: List[SrcExpr]

    def _make_list(self, l: List[SrcExpr]) -> SrcExpr:
        if l == []:
            return SrcNil()
        
        return SrcAnonAbs(
            SrcApp(
                SrcApp(
                    SrcAnonVar(0),
                    l[0],
                ),
                self._make_list(l[1:])
            )
        )

    def simplify(self) -> SimpleExpr:
        return self._make_list(self.elements).simplify()
        
@dataclass
class SrcByte(SrcExpr):
    """I/O byte as a list of bools"""
    value: int

    def simplify(self) -> SimpleExpr:
        bits = ((self.value >> (7 - i)) & 1 for i in range(0, 8))
        srcbool_list: List[SrcExpr] = [SrcBool(not bool(bit)) for bit in bits]
        return SrcList(srcbool_list).simplify()

@dataclass
class SrcStr(SrcExpr):
    """List of bytes"""
    value: str

    def simplify(self) -> SimpleExpr:
        srcbyte_list: List[SrcExpr] = [SrcByte(b) for b in bytes(self.value, encoding="utf-8")]
        return SrcList(srcbyte_list).simplify()

@dataclass
class SrcDefine(SrcExpr):
    """Define a variable. Can only be used inside a SrcBlock, since definitions
    can depend on their siblings"""
    var_name: str
    value: SrcExpr

    def simplify(self) -> SimpleExpr:
        raise NotImplementedError("SrcDefine must be part of a SrcBlock!")

@dataclass
class SrcLet(SrcExpr):
    """Let binding with multiple variables"""
    bindings: List[Tuple[str, SrcExpr]]
    expr: SrcExpr

    def _make_let(self, bindings: List[Tuple[str, SrcExpr]]) -> SrcExpr:
        if bindings == []:
            return self.expr
        name, value = bindings[0]
        return SrcApp(
            SrcAbs(
                name,
                self._make_let(bindings[1:]),
            ),
            value,
        )

    def simplify(self) -> SimpleExpr:
        return self._make_let(self.bindings).simplify()

@dataclass
class SrcBlock(SrcExpr):
    """A block of multiple statements. Define statements will be "hoisted" to
    the top and their definitions can be used in any statement in the block,
    regardless of order. Recursion is allowed among defined expressions. Other
    statements will be executed sequentially."""
    statements: List[SrcExpr]

    Y = dbn_to_srcexpr("λ [λ [1 [0 0]] λ [1 [0 0]]]")

    # "Statements" will depend on the type system a bit. Each sequential
    # statement must evaluate to nil, otherwise behavior is undefined.
    def _make_sequence(self, statements: List[SrcExpr]) -> SrcExpr:
        if not statements:
            return SrcVar("if")
        return SrcApp(
            statements[0],
            self._make_sequence(statements[1:]),
        )

    def simplify(self) -> SimpleExpr:
        # This should pad out the paper pretty nice!

        definitions = {}
        sequence = []

        for statement in self.statements:
            if isinstance(statement, SrcDefine):
                # Gather all the `define` statements
                if statement.var_name in definitions:
                    raise ValueError(f"{statement.var_name} is already defined!")

                # Simplify the definition value ASAP to avoid computing the
                # same simplification multiple times
                definitions[statement.var_name] = statement.value.simplify()
            else:
                # Run the other statements sequentially
                sequence.append(statement)

        # Set of names defined in the `define` statements
        defined_names = frozenset(definitions.keys())

        # Build a dependency graph
        G = nx.DiGraph()

        # Keep track of the definitions that directly refer to themselves.
        # These will be the only element in their SCC, but we still want to
        # apply the ordinary Y combinator.
        directly_recursive = set()

        for i, var_name in enumerate(definitions):
            value = definitions[var_name]
            G.add_node(var_name)
            references = sorted(list(value.get_references() & defined_names))
            if var_name in references:
                directly_recursive.add(var_name)

            # Edge from A to B means B depends on A.
            G.add_edges_from((d, var_name) for d in references)

        bindings: List[Tuple[str, SrcExpr]] = []

        # Find the DAG of SCCs in G
        C = nx.condensation(G)
        sorted_C = nx.topological_sort(C)

        for node in sorted_C:
            scc = C.nodes[node]["members"]
            if len(scc) == 1:
                var_name, = scc
                if var_name in directly_recursive:
                    # directly recursive, apply ordinary Y combinator
                    print("Found directly recursive function", var_name, file=sys.stderr)
                    fixed = SrcApp(
                        self.Y,
                        SrcAbs(var_name, definitions[var_name]),
                    )
                    bindings.append((var_name, fixed))
                else:
                    # not recursive, add regular binding
                    bindings.append((var_name, definitions[var_name]))
            else:
                print("Found indirect recursion among", scc, file=sys.stderr)
    
                func_list = SrcList([definitions[var_name] for var_name in scc])

                # Merge each function in the SCC into one "multiplexing"
                # function which switches behavior depending on its Nat
                # argument

                # The mux gets a unique name, like
                # mux-odd-even-8fe86920-b389-4f0a-b94d-aefb6e9f38ae
                mux_name = "-".join(("mux", "-".join(scc), str(uuid4())))

                # Implement the mux as a list of functions that gets indexed by
                # the argument
                mux = SrcAnonAbs(
                    SrcCall(SrcVar("list-ref"), [
                        func_list,
                        SrcAnonVar(0)
                    ])
                )

                # To allow recursive calls from inside the mux, each function
                # needs to be bound to the fixpoint applied to the function's
                # index in the list
                mux_bindings: List[Tuple[str, SrcExpr]] = []
                for i, var_name in enumerate(scc):
                    mux_bindings.append((var_name, SrcApp(SrcVar(mux_name), SrcNat(i))))

                # Apply the Y combinator
                fixed = SrcApp(
                    self.Y,
                    SrcAbs(mux_name, SrcLet(mux_bindings, mux))
                )
        
                bindings.append((mux_name, fixed))
                # Outside the fixpoint, each muxed function needs to be bound
                # to the fixed mux applied to its index
                for i, var_name in enumerate(scc):
                    bindings.append((var_name, SrcApp(SrcVar(mux_name), SrcNat(i))))

        if bindings:
            return SrcLet(
                bindings,
                self._make_sequence(sequence)
            ).simplify()
        return self._make_sequence(sequence).simplify()

# Built-in functions that are more "standard library" than "language feature"

# Built-in functions can refer to other built-ins (or themselves) and SrcBlock
# and SrcRoot will work out the recursion/dependencies.

# Index a list. The name comes from Scheme
list_ref = SrcLambda(["l", "i"], 
    SrcApp(SrcVar("fst"),
        SrcCall(SrcVar("i"), [SrcVar("snd"), SrcVar("l")])))

# simpler builtins
builtins = {
    "print": SrcAnonAbs(SrcApp(SrcAnonVar(0), SrcVar("output"))),
    "if": dbn_to_srcexpr("λ 0"),
    "pair": dbn_to_srcexpr("λλλ [[0 2] 1]"),
    "cons": SrcVar("pair"),
    "or": dbn_to_srcexpr("λλ [[0 0] 1]"),
    "and": dbn_to_srcexpr("λλ [[0 1] 0]"),
    "not": dbn_to_srcexpr("λλλ [[2 0] 1]"),
    "xor": dbn_to_srcexpr("λλ [[1 λλ [[2 0] 1]] 0]"),
    "is-zero": dbn_to_srcexpr("λλλ [[2 λ 1] 1]"),
    "is-nil": dbn_to_srcexpr("λ [[0 λλλ λλ0] λλ1]"),
    "**": dbn_to_srcexpr("λλ [0 1]"),
    "*": dbn_to_srcexpr("λλλ [2 [1 0]]"),
    "++": dbn_to_srcexpr("λλλ [1 [[2 1] 0]]"),
    "--": dbn_to_srcexpr("λλλ [[[2 λλ [0 [1 3]]] λ 1] λ 0]"),
    "+": dbn_to_srcexpr("λλλλ [[3 1] [[2 1] 0]]"),
    "-": dbn_to_srcexpr("λλ [[0 λλλ [[[2 λλ [0 [1 3]]] λ 1] λ 0]] 1]"),
    "%": dbn_to_srcexpr("λλλλ [[[3 λ [0 λλ 1]] [[3 λ [[[3 λλλ [[0 [2 [5 1]]] 1]] λ 1] 1]] λ 1]] λλ 0]"),
    # "%": dbn_to_srcexpr("λλλλ [[[3 λ [0 λλ 1]] [[3 λ [[[3 λλλ [[0 [2 [5 1]]] 1]] λ 1] 1]] λ 1]] λλ 0]"),
    "min": dbn_to_srcexpr("λλλλ [[[3 λλ [0 1]] λ1] [[2 λλ [3 [0 1]]] λ1]]"),
    "/": dbn_to_srcexpr("λλλλ [[[3 λλ [0 1]] λ 1] [[3 λ [[[3 λλ [0 1]] λ [3 [0 1]]] λ0]] 0]]"),
    "=": dbn_to_srcexpr("λλ [[[[1 λ [[0 λ0] λ0]] [[0 λλλ [1 2]] λλ0]] λλλ0] λλ1]"),
    "<=": dbn_to_srcexpr("λλ [[[1 λλ [0 1]] λλλ1] [[0 λλ [0 1]] λλλ0]]"),
    "<": dbn_to_srcexpr("λλ [[[0 λλ [0 1]] λλλ0] [[1 λλ [0 1]] λλλ1]]"),
    "fac": dbn_to_srcexpr("λλ [[[1 λλ [0 [1 λλ [[2 1] [1 0]]]]] λ1] λ0]"),
    "fst": SrcAnonAbs(SrcApp(SrcAnonVar(0), SrcBool(True))),
    "snd": SrcAnonAbs(SrcApp(SrcAnonVar(0), SrcBool(False))),
    "head": SrcVar("fst"),
    "tail": SrcVar("snd"),
    "list-ref": list_ref,
    "#t": SrcBool(True),
    "#f": SrcBool(False),
    "nil": SrcNil(),
}

@dataclass
class SrcRoot(SrcExpr):
    """Root node of a program. Finds all builtin values the program references
    and adds bindings for them, then binds input (gro) and output."""

    block: SrcExpr

    def simplify(self) -> SimpleExpr:
        simplified_block = self.block.simplify()

        builtin_defines = []

        expr = SrcBlock([simplified_block]).simplify()

        # The very act of defining a builtin may introduce other builtins, so
        # we have to repeatedly define builtins and re-check the entire root
        # block until there are no more undefined builtins
        while undefined_builtins := expr.get_references() & frozenset(builtins.keys()):
            # sort since frozenset order isn't guaranteed (cause Python hashes are
            # nondeterministic!?)
            for builtin in sorted(list(undefined_builtins)):
                simplified_builtin = builtins[builtin].simplify()
                builtin_defines.append(SrcDefine(builtin, simplified_builtin))
            expr = SrcBlock([*builtin_defines, simplified_block]).simplify()

        print("Found builtins", [define.var_name for define in builtin_defines], file=sys.stderr)

        return SrcAbs("input", SrcAbs("output", expr)).simplify()

# Parsing

# Source code => stream of tokens => ParseExpr (parse tree) => SrcExpr (AST)

@dataclass
class Token:
    """A """
    start: int
    end: int
    s: str

class ParseError(Exception):
    """Error during some part of the parsing process."""
    def __init__(self, message: str, index: Optional[int]=None):
        super().__init__(message)
        self.message = message
        self.index = index
    def format(self, src: str) -> str:
        """Given the original source code, `src`, format a nice error message
        that has the line with the error and a '^' pointing to where it
        happened."""
        if self.index is not None:
            c = 0
            # loop through lines until we find which line `index` is on
            for line_number, line in enumerate(src.splitlines()):
                if c <= self.index < c + len(line):
                    char = self.index - c

                    # handle indentation with tabs: len("\t") is 1, but it will
                    # be printed as 8 characters
                    padding = len(line[:char].expandtabs(8))

                    return "\n".join((
                        f"Parse error, line {line_number}:",
                        self.message,
                        line,
                        " " * padding + "^",
                    ))
                c += len(line) + 1 # for newline
        return f"Parse error:\n{self.message}"

# https://github.com/python/mypy/issues/5374
@dataclass # type: ignore[misc] 
class ParseExpr(ABC):
    start: int
    end: int

    @abstractmethod
    def to_srcexpr(self) -> SrcExpr:
        pass

    def collapse(self) -> "ParseExpr":
        return self

@dataclass
class ParseReserved(ParseExpr):
    s: str

    def to_srcexpr(self) -> SrcExpr:
        # A reserved word like "define" should never appear by itself
        raise ParseError("Unexpected reserved word!", self.start)

@dataclass
class ParseNat(ParseExpr):
    value: int

    def to_srcexpr(self) -> SrcExpr:
        return SrcNat(self.value)

@dataclass
class ParseSymbol(ParseExpr):
    s: str

    def to_srcexpr(self) -> SrcExpr:
        return SrcVar(self.s)

@dataclass
class ParseStr(ParseExpr):
    s: str

    def to_srcexpr(self) -> SrcExpr:
        return SrcStr(self.s)

@dataclass
class ParseBlock(ParseExpr):
    statements: Sequence[ParseExpr]

    def to_srcexpr(self) -> SrcExpr:
        return SrcBlock([statement.to_srcexpr() for statement in self.statements])

@dataclass
class ParseList(ParseExpr):
    elements: Sequence[ParseExpr]

    def to_srcexpr(self) -> SrcExpr:
        return SrcList([element.to_srcexpr() for element in self.elements])

@dataclass
class ParseTree(ParseExpr):
    children: Sequence[ParseExpr]

    def collapse(self) -> ParseExpr:
        """Collapse a tree with 1 child down to just its child. Reduces
        ((BLAH)) to just BLAH."""
        if len(self.children) == 1:
            return self.children[0].collapse()
        return self

    def _lambda_to_srcexpr(self) -> SrcExpr:
        var_symbols = self.children[1]
        var_names: List[str] = []

        if isinstance(var_symbols, ParseSymbol):
            # lambda with a single argument
            var_names.append(var_symbols.s)

        elif isinstance(var_symbols, ParseTree):
            # lambda with multiple arguments
            for var_symbol in var_symbols.children:
                if not isinstance(var_symbol, ParseSymbol):
                    raise ParseError("Expected parameter name!", var_symbol.start)
                var_names.append(var_symbol.s)
        else:
            raise ParseError("Expected parameter list to follow 'lambda'!", var_symbol.start)

        try:
            body = self.children[2]
        except IndexError as e:
            raise ParseError("Expected 'lambda' body!", self.end) from e

        return SrcLambda(var_names, body.to_srcexpr())

    def _let_to_srcexpr(self) -> SrcExpr:
        var_symbol = self.children[1]

        if not isinstance(var_symbol, ParseSymbol):
            raise ParseError("Expected variable name!", var_symbol.start)
        
        var_name = var_symbol.s

        try:
            value = self.children[2]
        except IndexError as e:
            raise ParseError("Expected bound value!", self.end) from e

        try:
            body = self.children[3]
        except IndexError as e:
            raise ParseError("Expected 'let' body!", self.end) from e

        binding = (var_name, value.to_srcexpr())
        return SrcLet([binding], body.to_srcexpr())

    def _define_to_srcexpr(self) -> SrcExpr:
        # same as let_to_srcexpr
        var_symbol = self.children[1]

        if not isinstance(var_symbol, ParseSymbol):
            raise ParseError("Expected variable name!", var_symbol.start)
        
        var_name = var_symbol.s

        try:
            value = self.children[2]
        except IndexError as e:
            raise ParseError("Expected defined value!", self.end) from e

        return SrcDefine(var_name, value.to_srcexpr())

    def to_srcexpr(self) -> SrcExpr:
        if not self.children:
            return SrcNil()

        if len(self.children) == 1:
            return self.children[0].to_srcexpr()

        if isinstance(self.children[0], ParseReserved):
            word = self.children[0].s

            if word == "lambda":
                return self._lambda_to_srcexpr()
            if word == "let":
                return self._let_to_srcexpr()
            if word == "define":
                return self._define_to_srcexpr()
                
            raise ParseError("Unknown word!", self.children[0].start)

        func = self.children[0].to_srcexpr()
        args = [child.to_srcexpr() for child in self.children[1:]]
        return SrcCall(func, args)


# Adapted from https://norvig.com/lispy2.html
tokenizer = r'''(?:\s|;[^\n]*\n)*(,@|[()[\]]|"(?:\\.|[^"\\])*"|;.*|[^\s(";)[\]]*)(.*)'''

def tokenize(src: str) -> Generator[Token, None, None]:
    """Convert source code to a stream of tokens"""
    index = 0

    # DOTALL flag to treat newlines as regular whitespace
    while src_match := re.match(tokenizer, src, flags=re.DOTALL):
        token_str, src = src_match.groups()
        token_span, remaining_span = src_match.span(1), src_match.span(2)

        # If we didn't find any token, raise an error
        if remaining_span[0] == 0:
            raise ParseError("Unexpected character", index)

        if token_str != "":
            yield Token(index + token_span[0], index + token_span[1], token_str)

        index += remaining_span[0]

        # If there's no more source code to tokenize, return
        if not src:
            return

reserved_words = {"lambda", "define", "let"}

def tokens_to_parseexpr(src: str, tokens: Iterator[Token]) -> ParseExpr:
    """Convert a stream of tokens to a parse tree"""

    # https://norvig.com/lispy2.html

    def read_ahead(token: Token) -> ParseExpr:
        if token.s in ")}]":
            # Should never be a lonely close paren/brace/bracket
            raise ParseError(f"Unexpected '{token.s}'", token.start)
        if token.s == "(":
            children = []

            while (t := next(tokens)).s != ")":
                children.append(read_ahead(t))

            return ParseTree(token.start, t.end, children).collapse()
        if token.s == "{":
            statements = []

            while (t := next(tokens)).s != "}":
                statements.append(read_ahead(t))

            return ParseBlock(token.start, t.end, statements)

        if token.s == "[":
            elements = []

            while (t := next(tokens)).s != "]":
                elements.append(read_ahead(t))

            return ParseList(token.start, t.end, elements)

        if token.s in reserved_words:
            return ParseReserved(token.start, token.end, token.s)

        # Match nat literal
        if nat_match := re.search(r"^(\d+)(.*)", token.s):
            value = int(nat_match.group(1))
            remainder = nat_match.group(2)

            if remainder:
                index = token.start + nat_match.span(2)[0]
                raise ParseError(f"Unexpected character while parsing nat!", index)
            return ParseNat(token.start, token.end, value)

        # Match string literal
        if str_match := re.search(r'''^"((?:\\.|[^"\\])*)"$''', token.s):
            escaped = str_match.group(0)

            # E.g., convert "\n" to actual newline
            unescaped = literal_eval(escaped)
            return ParseStr(token.start, token.end, unescaped)

        return ParseSymbol(token.start, token.end, token.s)

    return read_ahead(next(tokens))


def parse_expr(src: str) -> SrcExpr:
    tokens = tokenize(src)
    try:
        return tokens_to_parseexpr(src, tokens).to_srcexpr()
    except StopIteration:
        raise ParseError("Unexpected end of input. Maybe an unmatched '('?")


def parse(src: str) -> SrcExpr:
    """Convert source code to AST"""
    tokens = peekable(tokenize(src))

    statements: List[ParseExpr] = []

    # There is an implicit block at the top level of the document, so there may
    # be multiple statements to parse.

    while True:
        try:
            statements.append(tokens_to_parseexpr(src, tokens))
        except StopIteration:
            raise ParseError("Unexpected end of input. Maybe an unmatched '('?")
        
        # Check to see if there's another statement after
        try:
            tokens.peek()
        except StopIteration:
            # If there isn't, we are done parsing
            break

    srcexpr = ParseBlock(0, len(src), statements).to_srcexpr()
    return SrcRoot(srcexpr)

# More complex builtins
builtins["map"] = parse_expr("""
(lambda (f l)
    ((is-nil l)
        nil
        (cons (f (fst l)) (map f (snd l)))))
""")

builtins["concat"] = parse_expr("""
(lambda (list-a list-b)
    ((is-nil list-a)
        list-b
        (cons (fst list-a) (concat (tail list-a) list-b))))
""")

nat_to_str = parse_expr("""
(lambda n
    (let last-digit
        (list-ref ["0" "1" "2" "3" "4" "5" "6" "7" "8" "9"] (% n 10))
    (let n-div-10
        (/ n 10)
    ((is-zero n-div-10)
        last-digit
        (concat (nat->str n-div-10) last-digit)))))
""")
builtins["nat->str"] = nat_to_str

def dbn_to_blc(dbn: str) -> str:
    # Fortified version of Justine's compile.sh

    binary: List[str] = []

    while dbn:
        char = dbn[0]
        if char == "λ":
            binary.extend("00")
            dbn = dbn[1:]
        elif char == "[":
            binary.extend("01")
            dbn = dbn[1:]
        elif index_match := re.search(r"^(\d+)(.*)", dbn):
            index = int(index_match.group(1))
            remainder = index_match.group(2)
            binary.extend((index * "1") + "10")
            dbn = remainder
        else:
            dbn = dbn[1:]

    return "".join(binary)


def exec_dbn(dbn: str, input: str="", capture: bool=False) -> Optional[str]:
    """Execute de Bruijn notation BLC. Optionally capture stdout."""
    blc = dbn_to_blc(dbn)
    Blc = run(["justine/asc2bin.com"], input=blc.encode("utf-8"), stdout=PIPE).stdout

    print("Output is ", len(Blc), "bytes.", file=sys.stderr)

    if capture:
        p = run([PATH_TO_BLC_INTERPRETER, "-b"], input=Blc + input.encode("utf-8"), stdout=PIPE)
        return p.stdout.decode("utf-8")
    else:
        run([PATH_TO_BLC_INTERPRETER, "-b"], input=Blc + input.encode("utf-8"))
        return None


def exec_srcexpr(srcexpr: SrcExpr, input: str="", capture: bool=False) -> Optional[str]:
    """Execute a SrcExpr. Optionally capture stdout."""
    return exec_dbn(srcexpr.to_dbn({}), input, capture)

if __name__ == "__main__":
    # Put your own program here! TODO command-line interface

    # src = '''
# (define factorial
    # (lambda n
    #     (if (is-zero n) 
    #         (1)
    #         (* n (factorial (-- n))))))
    # (print (nat->str (factorial 4)))
    # '''

    src = '''
    (define a [1 22 3])
    (define b [4 5 58])
    ; comment
    (print (nat->str (list-ref (concat a b) 5)))
    '''

    try:
        srcexpr = parse(src)
        exec_srcexpr(srcexpr)
    except ParseError as e:
        print(e.format(src), file=sys.stderr)
