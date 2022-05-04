#!/usr/bin/env python3

"""
TODO list
    typing?
    parsing
    nice builtin library
        https://en.wikipedia.org/wiki/Church_encoding#Signed_numbers
        nat->str
        str->nat
        map
        reduce
        sort would be cool
"""

# "A language targeting SectorLambda sounds super cool." -Justine Tunney

from typing import Dict, Generator, Iterator, Tuple, NamedTuple, List, FrozenSet, Optional, Sequence
from dataclasses import dataclass
from abc import ABC, abstractmethod
import sys
import re
from uuid import uuid4
from subprocess import run, PIPE

# For reasoning about indirect recursion
import networkx as nx

from more_itertools import peekable

# Raise the stack limit or we hit the maximum recursion depth, maybe Python was
# a bad choice
import resource, sys
resource.setrlimit(resource.RLIMIT_STACK, (2**29,-1))
sys.setrecursionlimit(10**6)

# Use our build of the Blc interpreter
PATH_TO_BLC_INTERPRETER = "./lambda"


# Target language (de Bruijn notation Blc)
class TgtExpr(ABC):
    """A lambda calculus expression"""
    @abstractmethod
    def to_dbn(self) -> str:
        """Convert to de Bruijn notation"""
        pass

@dataclass
class TgtAbs(TgtExpr):
    """Abstraction (a "λ" followed by an expression)"""
    expr: TgtExpr

    def to_dbn(self) -> str:
        return f"λ {self.expr.to_dbn()}"

@dataclass
class TgtApp(TgtExpr):
    """Function application"""
    function: TgtExpr
    argument: TgtExpr

    def to_dbn(self) -> str:
        return f"[{self.function.to_dbn()} {self.argument.to_dbn()}]"

@dataclass
class TgtVar(TgtExpr):
    """A variable. In DBN, variables are referenced by their "index", or the
    number of abstractions since the variable was bound, instead of by a
    name."""
    index: int
    def to_dbn(self) -> str:
        return str(self.index)

# Source language (our Lisp)

Context = Dict[str, int]

class SrcExpr(ABC):
    """An expression in the source language"""

    @abstractmethod
    def simplify(self) -> "SimpleExpr":
        """Convert to a simplified subset of the source language"""
        pass

    def compile(self, context: Context) -> TgtExpr:
        """Convert this expression to an equivalent expression in lambda
        calculus. The `context` parameter maps variable names to their de
        Bruijn indices"""
        return self.simplify().compile(context)

class SimpleExpr(SrcExpr):
    """Intermediate, simplified subset of source language. We convert to this
    intermediate representation to figure out which variables an expression
    references. `get_references` is easy to compute in the simplified language,
    since only SrcVars can make references, but awkward in the source
    language."""
    @abstractmethod
    def compile(self, context: Context) -> TgtExpr:
        pass

    @abstractmethod
    def get_references(self) -> frozenset[str]:
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

    def compile(self, context: Context) -> TgtExpr:
        # Increment the de Bruijn index of each variable already bound
        new_context = {k: v + 1 for k, v in context.items()}

        # and set the index of the newly-bound variable to 0
        new_context[self.var_name] = 0
        return TgtAbs(self.expr.compile(new_context))

@dataclass
class SrcAnonAbs(SimpleExpr):
    """Abstraction with an unnamed variable. Used for translating de Bruijn
    lambda calculus directly into the source language."""
    expr: SrcExpr

    def get_references(self) -> frozenset[str]:
        return self.expr.simplify().get_references()

    def simplify(self) -> SimpleExpr:
        return SrcAnonAbs(self.expr.simplify())

    def compile(self, context: Context) -> TgtExpr:
        new_context = {k: v + 1 for k, v in context.items()}
        return TgtAbs(self.expr.compile(new_context))

@dataclass
class SrcVar(SimpleExpr):
    """Named variable"""
    name: str

    def get_references(self) -> frozenset[str]:
        return frozenset((self.name,))

    def simplify(self) -> SimpleExpr:
        return self

    def compile(self, context: Context) -> TgtExpr:
        # Look up the variable's index in the `context`
        return TgtVar(context[self.name])

@dataclass
class SrcAnonVar(SimpleExpr):
    """Unnamed variable with only an index. Directly corresponds to TgtVar."""
    index: int

    def get_references(self) -> frozenset[str]:
        return frozenset()

    def simplify(self) -> SimpleExpr:
        return self

    def compile(self, context: Context) -> TgtExpr:
        return TgtVar(self.index)

@dataclass
class SrcApp(SimpleExpr):
    """Function application. Directly corresponds to TgtApp."""
    function: SrcExpr
    argument: SrcExpr

    def get_references(self) -> frozenset[str]:
        return self.function.simplify().get_references() | self.argument.simplify().get_references()

    def simplify(self) -> SimpleExpr:
        return SrcApp(self.function.simplify(), self.argument.simplify())

    def compile(self, context: Context) -> TgtExpr:
        return TgtApp(self.function.compile(context), self.argument.compile(context))

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
        elif char in "012346789":
            return SrcAnonVar(int(char)), dbn[1:]
        else:
            return dbn_to_srcexpr_rem(dbn[1:])

    return dbn_to_srcexpr_rem(dbn)[0]

@dataclass
class SrcCall(SrcExpr):
    """Function application with multiple arguments."""

    function: SrcExpr
    arguments: List[SrcExpr]

    def make_call(self, arguments: List[SrcExpr]) -> SrcExpr:
        if not arguments:
            return SrcApp(self.function, SrcNil())
        if len(arguments) == 1:
            return SrcApp(self.function, arguments[0])
        return SrcApp(self.make_call(arguments[:-1]), arguments[-1])

    def simplify(self) -> SimpleExpr:
        return self.make_call(self.arguments).simplify()

@dataclass
class SrcLambda(SrcExpr):
    """TODO Function definition with multiple arguments"""
    var_names: List[str]
    expr: SrcExpr

    def make_lambda(self, var_names: List[str]) -> SrcExpr:
        if not var_names:
            return SrcAnonAbs(self.expr)
        if len(var_names) == 1:
            return SrcAbs(var_names[0], self.expr)
        return SrcAbs(var_names[0], self.make_lambda(var_names[1:]))

    def simplify(self) -> SimpleExpr:
        return self.make_lambda(self.var_names).simplify()

@dataclass
class SrcNat(SrcExpr):
    """Church numeral"""
    value: int

    def __post_init__(self) -> None:
        if self.value < 0:
            raise ValueError("Nat cannot be less than 0!")

    def make_nat(self, n: int) -> SrcExpr:
        if n == 0:
            return SrcAnonVar(0)
        return SrcApp(
                SrcAnonVar(1),
                self.make_nat(n - 1)
            )

    def simplify(self) -> SimpleExpr:
        return SrcAnonAbs(SrcAnonAbs(
            self.make_nat(self.value)
        )).simplify()

@dataclass
class SrcBool(SrcExpr):
    """Boolean. λλ 0 is false, λλ 1 is true."""
    value: bool

    def simplify(self) -> SimpleExpr:
        return dbn_to_srcexpr(f"λλ {int(self.value)}")

# Might want `pair` in the language rather than a builtin for type checking
# purposes
# @dataclass
# class SrcPair(SrcExpr):
#     a: SrcExpr
#     b: SrcExpr
    
#     def get_references(self):
#         return frozenset(("pair"),) | self.a.get_references() | self.b.get_references()

#     def compile(self, context) -> TgtExpr:
#         return SrcApp(
#             SrcApp( 
#                 SrcVar("pair"),
#                 self.a
#             ),
#             self.b
#         ).compile(context)

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

    def make_list(self, l: List[SrcExpr]) -> SrcExpr:
        if l == []:
            return SrcNil()
        return SrcAnonAbs(
            SrcApp(
                SrcApp(
                    SrcAnonVar(0),
                    l[0],
                ),
                self.make_list(l[1:])
            )
        )

    def simplify(self) -> SimpleExpr:
        return self.make_list(self.elements).simplify()
        
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
    bindings: List[Tuple[str, SrcExpr]]
    expr: SrcExpr

    def make_let(self, bindings: List[Tuple[str, SrcExpr]]) -> SrcExpr:
        if bindings == []:
            return self.expr
        name, value = bindings[0]
        return SrcApp(
            SrcAbs(
                name,
                self.make_let(bindings[1:]),
            ),
            value,
        )

    def simplify(self) -> SimpleExpr:
        return self.make_let(self.bindings).simplify()

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
    def make_sequence(self, statements: List[SrcExpr]) -> SrcExpr:
        if not statements:
            return SrcVar("if")
        return SrcApp(
            statements[0],
            self.make_sequence(statements[1:]),
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
                self.make_sequence(sequence)
            ).simplify()
        return self.make_sequence(sequence).simplify()

# Built-in functions that are more "standard library" than "language feature"
# TODO once parsing works, these can be defined in the source language.

# Built-in functions can refer to other built-ins (or themselves) and SrcBlock
# and SrcRoot will work out the recursion/dependencies.

# TODO make a proper base-10 nat->str
cons_S = SrcAbs("str", SrcCall(SrcVar("pair"), [SrcByte(83), SrcVar("str")]))
nat_to_str = SrcAbs("n", 
    SrcCall(SrcVar("n"), [cons_S, SrcStr("")]),
)

# Index a list. The name comes from Scheme
list_ref = SrcLambda(["l", "i"], 
    SrcApp(SrcVar("fst"),
        SrcCall(SrcVar("i"), [SrcVar("snd"), SrcVar("l")])))

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
    "**": dbn_to_srcexpr("λλ [0 1]"),
    "*": dbn_to_srcexpr("λλλ [2 [1 0]]"),
    "++": dbn_to_srcexpr("λλλ [1 [[2 1] 0]]"),
    "--": dbn_to_srcexpr("λλλ [[[2 λλ [0 [1 3]]] λ 1] λ 0]"),
    "+": dbn_to_srcexpr("λλλλ [[3 1] [[2 1] 0]]"),
    "-": dbn_to_srcexpr("λλ [[0 λλλ [[[2 λλ [0 [1 3]]] λ 1] λ 0]] 1]"),
    "min": dbn_to_srcexpr("λλλλ [[[3 λλ [0 1]] λ1] [[2 λλ [3 [0 1]]] λ1]]"),
    "/": dbn_to_srcexpr("λλλλ [[[3 λλ [0 1]] λ 1] [[3 λ [[[3 λλ [0 1]] λ [3 [0 1]]] λ0]] 0]]"),
    # "%": dbn_to_srcexpr(""),
    "=": dbn_to_srcexpr("λλ [[[[1 λ [[0 λ0] λ0]] [[0 λλλ [1 2]] λλ0]] λλλ0] λλ1]"),
    "<=": dbn_to_srcexpr("λλ [[[1 λλ [0 1]] λλλ1] [[0 λλ [0 1]] λλλ0]]"),
    "<": dbn_to_srcexpr("λλ [[[0 λλ [0 1]] λλλ0] [[1 λλ [0 1]] λλλ1]]"),
    "nat->str": nat_to_str,
    "fac": dbn_to_srcexpr("λλ [[[1 λλ [0 [1 λλ [[2 1] [1 0]]]]] λ1] λ0]"),
    "car": SrcAnonAbs(SrcApp(SrcAnonVar(0), SrcBool(True))),
    "cdr": SrcAnonAbs(SrcApp(SrcAnonVar(0), SrcBool(False))),
    "fst": SrcVar("car"),
    "snd": SrcVar("cdr"),
    "list-ref": list_ref,
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

@dataclass
class Token:
    span: range
    s: str

class ParseError(Exception):
    def __init__(self, message: str, index: Optional[int]=None):
        super().__init__(message)
        self.message = message
        self.index = index
    def format(self, src: str) -> str:
        if self.index is not None:
            c = 0
            for line_number, line in enumerate(src.splitlines()):
                if c <= self.index < c + len(line):
                    return "\n".join((
                        f"Parse error, line {line_number}:",
                        self.message,
                        line,
                        " " * self.index + "^",
                    ))
                c += len(line)
        return f"Parse error:\n{self.message}"

# https://github.com/python/mypy/issues/5374
@dataclass # type: ignore[misc] 
class ParseExpr(ABC):
    span: range

    @abstractmethod
    def to_srcexpr(self) -> SrcExpr:
        pass

    def collapse(self) -> "ParseExpr":
        return self

@dataclass
class AtomReserved(ParseExpr):
    s: str

    def to_srcexpr(self) -> SrcExpr:
        raise ParseError("Unexpected reserved word!", self.span.start)

@dataclass
class AtomNat(ParseExpr):
    value: int

    def to_srcexpr(self) -> SrcExpr:
        return SrcNat(self.value)

@dataclass
class AtomSymbol(ParseExpr):
    s: str

    def to_srcexpr(self) -> SrcExpr:
        return SrcVar(self.s)

@dataclass
class AtomStr(ParseExpr):
    s: str

    def to_srcexpr(self) -> SrcExpr:
        return SrcStr(self.s)

@dataclass
class ParseBlock(ParseExpr):
    statements: Sequence[ParseExpr]

    def to_srcexpr(self) -> SrcExpr:
        return SrcBlock([statement.to_srcexpr() for statement in self.statements])

@dataclass
class ParseTree(ParseExpr):
    children: Sequence[ParseExpr]

    def collapse(self) -> ParseExpr:
        if len(self.children) == 1:
            return self.children[0].collapse()
        return self

    def lambda_to_srcexpr(self) -> SrcExpr:
        var_symbols = self.children[1]
        var_names: List[str] = []

        if isinstance(var_symbols, AtomSymbol):
            # lambda with a single argument
            var_names.append(var_symbols.s)
        elif isinstance(var_symbols, ParseTree):
            for var_symbol in var_symbols.children:
                if not isinstance(var_symbol, AtomSymbol):
                    raise ParseError("Expected parameter name!", var_symbol.span.start)
                var_names.append(var_symbol.s)
        else:
            raise ParseError("Expected parameter list to follow 'lambda'!", var_symbol.span.start)

        try:
            body = self.children[2]
        except IndexError as e:
            raise ParseError("Expected 'lambda' body!", self.span.stop) from e

        return SrcLambda(var_names, body.to_srcexpr())

    def let_to_srcexpr(self) -> SrcExpr:
        var_symbol = self.children[1]

        if not isinstance(var_symbol, AtomSymbol):
            raise ParseError("Expected variable name!", var_symbol.span.start)
        
        var_name = var_symbol.s

        try:
            value = self.children[2]
        except IndexError as e:
            raise ParseError("Expected bound value!", self.span.stop) from e

        try:
            body = self.children[3]
        except IndexError as e:
            raise ParseError("Expected 'let' body!", self.span.stop) from e

        binding = (var_name, value.to_srcexpr())
        return SrcLet([binding], body.to_srcexpr())

    def define_to_srcexpr(self) -> SrcExpr:
        # same as let_to_srcexpr
        var_symbol = self.children[1]

        if not isinstance(var_symbol, AtomSymbol):
            raise ParseError("Expected variable name!", var_symbol.span.start)
        
        var_name = var_symbol.s

        try:
            value = self.children[2]
        except IndexError as e:
            raise ParseError("Expected defined value!", self.span.stop) from e

        return SrcDefine(var_name, value.to_srcexpr())

    def to_srcexpr(self) -> SrcExpr:
        if not self.children:
            return SrcNil()

        if len(self.children) == 1:
            return self.children[0].to_srcexpr()

        if isinstance(self.children[0], AtomReserved):
            word = self.children[0].s

            if word == "lambda":
                return self.lambda_to_srcexpr()
            if word == "let":
                return self.let_to_srcexpr()
            if word == "define":
                return self.define_to_srcexpr()
                
            raise ParseError("Unknown word!", self.children[0].span.start)

        func = self.children[0].to_srcexpr()
        args = [child.to_srcexpr() for child in self.children[1:]]
        return SrcCall(func, args)


def tokenize(src: str) -> Generator[Token, None, None]:
    # Adapted from
    # https://stackoverflow.com/questions/45975769/lisp-tokenizer-from-character-stream-in-python#45978180

    current_word_start = 0

    # store as an list of characters since Python strings are immutable
    current_word: List[str] = []

    for i, c in enumerate(src):
        is_paren = c in "()"
        is_separator = c.isspace() or is_paren
        if not is_separator:
            if not current_word:
                current_word_start = i
            current_word.append(c)
        else:
            if current_word:
                value = "".join(current_word)
                yield Token(range(current_word_start, i + 1), value)
                current_word = []
            if is_paren:
                yield Token(range(i, i + 1), c)

reserved_words = {"lambda", "define", "let"}

def tokens_to_parseexpr(src: str, tokens: Iterator[Token]) -> ParseExpr:
    # https://norvig.com/lispy2.html

    def read_ahead(token: Token) -> ParseExpr:
        if token.s == ")":
            raise ParseError("Unexpected ')'", token.span.start)
        if token.s == "(":
            children = []

            while (t := next(tokens)).s != ")":
                children.append(read_ahead(t))

            return ParseTree(range(token.span.start, t.span.stop), children).collapse()
        if token.s == "{":
            statements = []

            while (t := next(tokens)).s != "}":
                statements.append(read_ahead(t))

            return ParseBlock(range(token.span.start, t.span.stop), statements)

        if token.s in reserved_words:
            return AtomReserved(token.span, token.s)

        if nat_match := re.search(r"^(\d+)(.*)", token.s):
            value = int(nat_match.group(1))
            remainder = nat_match.group(2)

            if remainder:
                index = token.span.start + nat_match.span(2)[0]
                raise ParseError(f"Unexpected character while parsing nat!", index)
            return AtomNat(token.span, value)

        return AtomSymbol(token.span, token.s)

    return read_ahead(next(tokens))


def parse(src: str) -> SrcExpr:
    tokens = peekable(tokenize(src))

    statements: List[ParseExpr] = []

    while True:
        try:
            statements.append(tokens_to_parseexpr(src, tokens))
        except StopIteration:
            raise ParseError("Unexpected end of input. Maybe an unmatched '('?")
        
        try:
            tokens.peek()
        except StopIteration:
            break

    srcexpr = ParseBlock(range(len(src)), statements).to_srcexpr()

    return SrcRoot(srcexpr)


def dbn_to_blc(dbn: str) -> str:
    # fortified version of Justine's compile.sh

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
    blc = dbn_to_blc(dbn)
    Blc = run(["justine/asc2bin.com"], input=blc.encode("utf-8"), stdout=PIPE).stdout

    if capture:
        p = run([PATH_TO_BLC_INTERPRETER, "-b"], input=Blc + input.encode("utf-8"), stdout=PIPE)
        return p.stdout.decode("utf-8")
    else:
        run([PATH_TO_BLC_INTERPRETER, "-b"], input=Blc + input.encode("utf-8"))
        return None


def exec_srcexpr(srcexpr: SrcExpr, input: str="", capture: bool=False) -> Optional[str]:
    return exec_dbn(srcexpr.compile({}).to_dbn(), input, capture)

if __name__ == "__main__":
    # Fibonacci example with direct recursion
    # fib = SrcAbs("n",
    #     SrcCall(SrcVar("if"), [
    #             SrcCall(SrcVar("<="), [SrcVar("n"), SrcNat(2)]),
    #             SrcNat(1),
    #             SrcCall(SrcVar("+"), [
    #                 SrcApp(SrcVar("fib"), SrcApp(SrcVar("--"), SrcVar("n"))),
    #                 SrcApp(SrcVar("fib"), SrcCall(SrcVar("-"), [SrcVar("n"), SrcNat(2)])),
    #             ])
    #         ]
    #     )
    # )
    # srcexpr = SrcRoot(
    #     SrcBlock([
    #         SrcDefine("fib", fib),
    #         SrcApp(SrcVar("print"),
    #             SrcApp(SrcVar("nat->str"), SrcApp(SrcVar("fib"), SrcNat(8))))
    #     ])
    # )

    # Even-odd example with mutual recursion 
    # even = SrcAbs("n",
    #     SrcCall(SrcVar("is-zero"), [
    #         SrcVar("n"),
    #         SrcBool(True),
    #         SrcApp(SrcVar("odd"), SrcApp(SrcVar("--"), SrcVar("n")))
    #     ])
    # )
    # odd = SrcAbs("n",
    #     SrcCall(SrcVar("is-zero"), [
    #         SrcVar("n"),
    #         SrcBool(False),
    #         SrcApp(SrcVar("even"), SrcApp(SrcVar("--"), SrcVar("n")))
    #     ])
    # )

    # n = 9
    # srcexpr = SrcRoot(
    #     SrcBlock([
    #         SrcDefine("odd", odd),
    #         SrcDefine("even", even),
    #         SrcApp(SrcVar("print"),
    #             SrcCall(SrcApp(SrcVar("even"), SrcNat(n)), [
    #                 SrcStr("even"),
    #                 SrcStr("odd"),
    #             ])
    #         ),
    #         SrcApp(SrcVar("print"), SrcStr("\n"))
    #     ])
    # )

    # Print nth char of input
    # n = 4
    # srcexpr = SrcRoot(
    #     SrcBlock([
    #         SrcApp(SrcVar("print"),
    #             SrcList([
    #                 SrcCall(SrcVar("list-ref"), [SrcVar("input"), SrcNat(n)]),
    #             ])
    #         ),
    #         SrcApp(SrcVar("print"), SrcStr("\n"))
    #     ])
    # )

    # tgtexpr = srcexpr.compile({})
    # dbn = tgtexpr.to_dbn()
    # print(dbn)
    # exec_dbn(tgtexpr.to_dbn())

    src = """
    (define (double) (lambda x (+ x x))) 
    (print (nat->str (double 1)))
    """

    try:
        srcexpr = parse(src)
        print(srcexpr)
        exec_srcexpr(parse(src))
    except ParseError as e:
        print(e.format(src), file=sys.stderr)
