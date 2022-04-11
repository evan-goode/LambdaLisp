#!/usr/bin/env python3

from typing import Dict, Tuple
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
    def compile(self, context: Dict[str, int]) -> TgtExpr:
        """Convert this expression to an equivalent expression in lambda
        calculus. The `context` parameter maps variable names to their de
        Bruijn indices"""
        pass

@dataclass
class SrcAbs(SrcExpr):
    """Abstraction. Eventually support multiple parameters."""
    var_name: str
    expr: SrcExpr

    def compile(self, context):
        # Increment the de Bruijn index of each variable already bound
        new_context = {k: v + 1 for k, v in context.items()}

        # and set the index of the newly-bound variable to 0
        new_context[self.var_name] = 0
        return TgtAbs(self.expr.compile(new_context))

@dataclass
class SrcAnonAbs(SrcExpr):
    """Abstraction with an unnamed variable. Used for translating de Bruijn
    lambda calculus directly into the source language"""
    expr: SrcExpr

    def compile(self, context):
        new_context = {k: v + 1 for k, v in context.items()}
        return TgtAbs(self.expr.compile(new_context))

@dataclass
class SrcVar(SrcExpr):
    """Named variable"""
    name: str

    def compile(self, context):
        # Look up the variable's index in the `context`
        return TgtVar(context[self.name])

@dataclass
class SrcAnonVar(SrcExpr):
    """Unnamed variable with only an index. Directly corresponds to TgtVar."""
    index: int

    def compile(self, context) -> TgtVar:
        return TgtVar(self.index)

@dataclass
class SrcApp(SrcExpr):
    """Function application. Directly corresponds to TgtApp."""
    function: SrcExpr
    argument: SrcExpr

    def compile(self, context) -> TgtApp:
        return TgtApp(self.function.compile(context), self.argument.compile(context))

def dbn_to_srcexpr(dbn: str) -> Tuple[SrcExpr, str]:
    """Convert de Bruijn notation lambda calculus directly to the source
    language. Useful for testing purposes, not sure whether we'll need this.
    Returns a SrcExpr and the remainder of the string that wasn't parsed."""
    char = dbn[0]
    if char == "λ":
        body, remaining = dbn_to_srcexpr(dbn[1:])
        return SrcAnonAbs(body), remaining
    elif char == "[":
        function, remaining = dbn_to_srcexpr(dbn[1:])
        argument, remaining = dbn_to_srcexpr(remaining[1:])
        return SrcApp(function, argument), remaining
    elif char in "012346789":
        return SrcAnonVar(int(char)), dbn[1:]
    else:
        return dbn_to_srcexpr(dbn[1:])

if __name__ == "__main__":
    nil = "λλ 0"
    omega = "λ [0 0]"
    
    # Example program to reverse the input string
    dbn = f"""λ [[0 [{omega}
       λλλλ [[1 [3 3]] λ [[0 3] 1]]]]
    {nil}]"""

    srcexpr, _ = dbn_to_srcexpr(dbn)

    print(srcexpr, file=sys.stderr)

    tgtexpr = srcexpr.compile({})

    print(tgtexpr.to_dbn())
