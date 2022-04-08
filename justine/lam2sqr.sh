#!/bin/sh
# converts lambda notation to expanded square notation, e.g.
#
#     $ ./lam2sqr.sh '(λf.(λx.f(xx))(λx.f(xx)))(λecs.s(λat.t(λb.ae(λx.b(c(λzy.x((λxy.λf.fxy)yz)))(e(λy.c(λz.xz(yz)))))(b(c(λz.zb))(λs.e(λx.c(λz.x(zb)))t)))))'
#     [λ [λ [1 [0 0]] λ [1 [0 0]]] λλλ [0 λλ [0 λ [[[2 5] λ [[1 [5 λλ [2 [[λλλ [[0 2] 1] 0] 1]]]] [6 λ [6 λ [[2 0] [1 0]]]]]] [[0 [4 λ [0 1]]] λ [[6 λ [6 λ [1 [0 3]]]] 2]]]]]]
#

lam2sqr() {
  o/lam2bin |
    o/blcdump -n 2>/dev/null
}

if [ $# -gt 0 ]; then
  printf %s "$*" | lam2sqr
else
  lam2sqr
fi
