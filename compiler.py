#!/usr/bin/env python3

"""
TODO list
    typing?
    parsing
    mutual recursion
    input
    nice builtin library
        https://en.wikipedia.org/wiki/Church_encoding#Signed_numbers
        nat->str
        str->nat
        map
        reduce
        sort would be cool
"""

# "A language targeting SectorLambda sounds super cool." -Justine Tunney

from typing import Dict, Tuple, List, FrozenSet
from dataclasses import dataclass
from abc import ABC, abstractmethod
import sys
import re

# For reasoning about indirect recursion
import networkx as nx

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
class SrcExpr(ABC):
    """An expression in the source language"""

    @abstractmethod
    def simplify(self) -> "SimpleExpr":
        """Convert to a simplified subset of the source language"""
        pass

    def compile(self, context: Dict[str, int]) -> TgtExpr:
        """Convert this expression to an equivalent expression in lambda
        calculus. The `context` parameter maps variable names to their de
        Bruijn indices"""
        return self.simplify().compile(context)

    def get_references(self) -> frozenset[str]:
        return self.simplify().get_references()

class SimpleExpr(SrcExpr):
    """Intermediate, simplified subset of source language. We convert to this
    intermediate representation to figure out which variables an expression
    references. `get_references` is easy to compute in the simplified language,
    since only SrcVars can make references, but awkward in the source
    language."""
    @abstractmethod
    def compile(self, context: Dict[str, int]) -> TgtExpr:
        pass

    @abstractmethod
    def get_references(self) -> frozenset[str]:
        pass

@dataclass
class SrcAbs(SimpleExpr):
    """Abstraction with a single named variable."""
    var_name: str
    expr: SrcExpr

    def get_references(self):
        # Don't count references to the bound variable
        return self.expr.get_references() - frozenset((self.var_name,))

    def simplify(self):
        return SrcAbs(self.var_name, self.expr.simplify())

    def compile(self, context):
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

    def get_references(self):
        return self.expr.get_references()

    def simplify(self):
        return SrcAnonAbs(self.expr.simplify())

    def compile(self, context):
        new_context = {k: v + 1 for k, v in context.items()}
        return TgtAbs(self.expr.compile(new_context))

@dataclass
class SrcVar(SimpleExpr):
    """Named variable"""
    name: str

    def get_references(self):
        return frozenset((self.name,))

    def simplify(self):
        return self

    def compile(self, context):
        # Look up the variable's index in the `context`
        return TgtVar(context[self.name])

@dataclass
class SrcAnonVar(SimpleExpr):
    """Unnamed variable with only an index. Directly corresponds to TgtVar."""
    index: int

    def get_references(self):
        return frozenset()

    def simplify(self):
        return self

    def compile(self, context) -> TgtVar:
        return TgtVar(self.index)

@dataclass
class SrcApp(SimpleExpr):
    """Function application. Directly corresponds to TgtApp."""
    function: SrcExpr
    argument: SrcExpr

    def get_references(self):
        return self.function.get_references() | self.argument.get_references()

    def simplify(self):
        return SrcApp(self.function.simplify(), self.argument.simplify())

    def compile(self, context) -> TgtApp:
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

    def simplify(self):
        return self.make_call(self.arguments).simplify()

# @dataclass
# class SrcLambda(SrcExpr):
#     """TODO Function definition with multiple arguments"""
#     pass

@dataclass
class SrcNat(SrcExpr):
    """Church numeral"""
    value: int

    def __post_init__(self):
        if self.value < 0:
            raise ValueError("Nat cannot be less than 0!")

    def make_nat(self, n: int):
        if n == 0:
            return SrcAnonVar(0)
        return SrcApp(
                SrcAnonVar(1),
                self.make_nat(n - 1)
            )

    def simplify(self):
        return SrcAnonAbs(SrcAnonAbs(
            self.make_nat(self.value)
        )).simplify()

@dataclass
class SrcBool(SrcExpr):
    """Boolean. λλ 0 is false, λλ 1 is true."""
    value: bool

    def simplify(self):
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
    nil = dbn_to_srcexpr("λλ 0")

    def simplify(self):
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

    def simplify(self):
        return self.make_list(self.elements).simplify()
        
@dataclass
class SrcByte(SrcExpr):
    """I/O byte as a list of bools"""
    value: int

    def simplify(self):
        bits = ((self.value >> (7 - i)) & 1 for i in range(0, 8))
        srcbool_list = [SrcBool(not bool(bit)) for bit in bits]
        return SrcList(srcbool_list).simplify()

@dataclass
class SrcStr(SrcExpr):
    """List of bytes"""
    value: str

    def simplify(self):
        srcbyte_list = [SrcByte(b) for b in bytes(self.value, encoding="utf-8")]
        return SrcList(srcbyte_list).simplify()

@dataclass
class SrcDefine(SrcExpr):
    var_name: str
    value: SrcExpr

    def simplify(self):
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

    def simplify(self):
        return self.make_let(self.bindings).simplify()

@dataclass
class SrcBlock(SrcExpr):
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

    def simplify(self):
        # This should pad out the paper pretty nice!

        definitions = {}
        sequence = []

        for statement in self.statements:
            if isinstance(statement, SrcDefine):
                # Gather all the `define` statements
                if statement.var_name in definitions:
                    raise ValueError(f"{statement.var_name} is already defined!")
                definitions[statement.var_name] = statement.value
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
                    fixed = SrcApp(
                        self.Y,
                        SrcAbs(var_name, definitions[var_name]),
                    )
                    bindings.append((var_name, fixed))
                else:
                    # not recursive, add regular binding
                    bindings.append((var_name, definitions[var_name]))
            else:
                # TODO mutual recursion
                pass

        if bindings:
            return SrcLet(
                bindings,
                self.make_sequence(sequence)
            ).simplify()
        return self.make_sequence(sequence).simplify()

# TODO make a proper base-10 nat->str
cons_S = SrcAbs("str", SrcCall(SrcVar("pair"), [SrcByte(83), SrcVar("str")]))
nat_to_str = SrcAbs("n", 
    SrcCall(SrcVar("n"), [cons_S, SrcStr("")]),
)

# Built-in functions that are more "standard library" than "language feature"
# TODO once parsing works, these can be defined in the source language.

# Built-in functions can refer to other built-ins (or themselves) and SrcBlock
# and SrcRoot will work out the recursion/dependencies.
builtins = {
    "print": SrcAnonAbs(SrcApp(SrcAnonVar(0), SrcVar("put"))),
    "if": dbn_to_srcexpr("λ 0"),
    "pair": dbn_to_srcexpr("λλλ [[0 2] 1]"),
    "or": dbn_to_srcexpr("λλ [[0 0] 1]"),
    "and": dbn_to_srcexpr("λλ [[0 1] 0]"),
    "not": dbn_to_srcexpr("λλλ [[2 0] 1]"),
    "xor": dbn_to_srcexpr("λλ [[1 λλ [[2 0] 1]] 0]"),
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
}

@dataclass
class SrcRoot(SrcExpr):
    """Root node of a program. Finds all builtin values the program references
    and adds bindings for them, then binds gro and put."""

    block: SrcExpr

    def simplify(self):
        # find all builtins used
        def get_referenced_builtins(expr: SrcExpr) -> frozenset[str]:
            used_by_expr = expr.get_references() & frozenset(builtins.keys())

            # built-ins may refer to other built-ins
            used_by_builtins = (get_referenced_builtins(builtins[name]) for name in used_by_expr)
            return frozenset.union(used_by_expr, *(used_by_builtins))

        # sort since frozenset order isn't guaranteed (cause Python hashes are
        # nondeterministic!?)
        referenced_builtins = sorted(list(get_referenced_builtins(self.block)))

        builtin_defines = [
            SrcDefine(name, builtins[name])
            for name in referenced_builtins
        ]

        body = SrcBlock([
            *builtin_defines,
            self.block,
        ])

        return SrcAbs("gro", SrcAbs("put", body)).simplify()

# def tokenize(s: str) -> Generator[str, None, None]
#     # Adapted from
#     # https://stackoverflow.com/questions/45975769/lisp-tokenizer-from-character-stream-in-python#45978180

#     # store as an list of characters since strings are immutable
#     current_word = []
#     for c in s:
#         is_paren = c in "()"
#         is_separator = c.isspace() or is_paren
#         if not is_separator:
#             current_word.append(c)
#         else:
#             if current_word:
#                 yield "".join(current_word)
#                 current_word = []
#             if is_paren:
#                 yield c

# def parse(s: str) -> SrcExpr:
    # tokens = tokenize(s)

if __name__ == "__main__":
    nil = "λλ 0"
    omega = "λ [0 0]"
    
    # Example program to reverse the input string
    # dbn = f"""λ [[0 [{omega}
    #    λλλλ [[1 [3 3]] λ [[0 3] 1]]]]
    # {nil}]"""

    # srcexpr, _ = dbn_to_srcexpr(dbn)

    # Fibonacci example with direct recursion
    fib = SrcAbs("n",
        SrcCall(SrcVar("if"), [
                SrcCall(SrcVar("<="), [SrcVar("n"), SrcNat(2)]),
                SrcNat(1),
                SrcCall(SrcVar("+"), [
                    SrcApp(SrcVar("fib"), SrcApp(SrcVar("--"), SrcVar("n"))),
                    SrcApp(SrcVar("fib"), SrcCall(SrcVar("-"), [SrcVar("n"), SrcNat(2)])),
                ])
            ]
        )
    )

    srcexpr = SrcRoot(
        SrcBlock([
            SrcDefine("fib", fib),
            SrcApp(SrcVar("print"), SrcApp(SrcVar("nat->str"), SrcApp(SrcVar("fib"), SrcNat(8)))),
        ])
    )

    tgtexpr = srcexpr.compile({})
    print(tgtexpr.to_dbn())
