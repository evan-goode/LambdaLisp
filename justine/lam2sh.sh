#!/bin/sh
# converts lambda notation to shell script notation, e.g.
#
#     $ ./lam2sh.sh '(λf.(λx.f(xx))(λx.f(xx)))(λecs.s(λat.t(λb.ae(λx.b(c(λzy.x((λxy.λf.fxy)yz)))(e(λy.c(λz.xz(yz)))))(b(c(λz.zb))(λs.e(λx.c(λz.x(zb)))t)))))'
#     [$Y λλλ [0 λλ [0 λ [[[2 5] λ [[1 [5 λλ [2 [[$pair 0] 1]]]] [6 λ [6 λ [[2 0] [1 0]]]]]] [[0 [4 λ [0 1]]] λ [[6 λ [6 λ [1 [0 3]]]] 2]]]]]]
#

lam2sh() {
  o/lam2bin |
    o/blcdump -N 2>/dev/null |
    sed '
        s/\\/λ/g
        s/\([^][[:space:][:cntrl:][:digit:]*+/^\λ][^][[:space:][:cntrl:][:digit:]\λ]*\)/$\1/g
      '
}

if [ $# -gt 0 ]; then
  printf %s "$*" | lam2sh
else
  lam2sh
fi
