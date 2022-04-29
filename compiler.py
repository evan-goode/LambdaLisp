#!/usr/bin/env python3

from typing import Dict, Tuple, List, FrozenSet
from dataclasses import dataclass
from abc import ABC, abstractmethod

import sys

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
        """Convert to a SimpleExpr and a set of references"""
        pass

    def get_references(self) -> frozenset[str]:
        return self.simplify().get_references()

# Simplified subset of source language
class SimpleExpr(SrcExpr):
    @abstractmethod
    def compile(self, context: Dict[str, int]) -> "TgtExpr":
        """Convert this expression to an equivalent expression in lambda
        calculus. The `context` parameter maps variable names to their de
        Bruijn indices"""
        pass

    @abstractmethod
    def get_references(self) -> frozenset[str]:
        pass

@dataclass
class SrcAbs(SimpleExpr):
    """Abstraction. Eventually support multiple parameters."""
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
    lambda calculus directly into the source language"""
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
class SrcNat(SrcExpr):
    """Natural number"""
    value: int

    def __post_init__(self):
        if self.value < 0:
            raise ValueError("Nat cannot be less than 0!")

    def make_nat(n: int):
        if n == 0:
            return SrcAnonVar(0)
        return SrcAnonAbs(
            SrcApp(
                SrcAnonVar(1),
                self.nat(n - 1)
            )
        )

    def simplify(self):
        return make_nat(self.value)

@dataclass
class SrcBool(SrcExpr):
    """Boolean. λλ 0 is false, λλ 1 is true."""
    value: bool

    def simplify(self):
        return dbn_to_srcexpr(f"λλ {int(self.value)}")

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
    elements: List[SrcExpr]

    def make_list(self, l: List[SrcExpr]):
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

# @dataclass
# class SrcBlock(SrcExpr):
#     statements: List[SrcExpr]

#     def compile(self, context) -> TgtExpr:
#         pass

@dataclass
class SrcLet(SrcExpr):
    bindings: List[Tuple[str, SrcExpr]]
    expr: SrcExpr

    def make_let(self, bindings) -> SrcExpr:
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

builtins = {
    "print": (
        SrcAbs("str", SrcApp(SrcVar("str"), SrcVar("put")))
    ),
    "pair": (
        dbn_to_srcexpr("λλλ [[0 2] 1]")
    ),
}

# @dataclass
# class SrcBuiltin(SrcExpr):
#     name: str

#     builtins = {
#         "print": (
#             SrcAbs("str", SrcApp(SrcVar("str"), SrcVar("put")))
#         ),
#         "pair": (
#             dbn_to_srcexpr("λλλ [[0 2] 1]")
#         ),
#     }

#     def __post_init__(self):
#         if self.name not in self.builtins:
#             raise ValueError(f"{self.name} is not a built-in expression")

#     def get_references(self):
#         return self.builtins[self.name].get_references()

#     def compile(self, context):
#         return self.builtins[self.name].compile(context)

@dataclass
class SrcRoot(SrcExpr):
    """Root node of a program. Finds all builtin values the program references
    and adds bindings for them, then binds gro and put."""

    block: SrcExpr

    def simplify(self):

        # find all builtins used
        referenced_builtins = self.block.get_references() & frozenset(builtins.keys())

        print("Found builtins:", referenced_builtins, file=sys.stderr)
    
        builtin_bindings = [
            (name, builtins[name])
            for name in referenced_builtins
        ]

        # TODO switch to define to allow recursive builtins
        body = SrcLet(
            builtin_bindings,
            self.block,
        )

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

    # Hello world example
    srcexpr = SrcRoot(
        SrcApp(
            SrcVar("print"),
            SrcStr("Hello world 🌎"),
        )
    )

    print(srcexpr, file=sys.stderr)

    simpleexpr = srcexpr.simplify()

    tgtexpr = simpleexpr.compile({})

    print(tgtexpr.to_dbn())
