#!/bin/sh
# converts square notation to lambda notation, e.g.
#
#     $ ./sqr2lam.sh '[λ [λ [1 [0 0]] λ [1 [0 0]]] λλλ [0 λλ [0 λ [[[2 5] λ [[1 [5 λλ [2 [[λλλ [[0 2] 1] 0] 1]]]] [6 λ [6 λ [[2 0] [1 0]]]]]] [[0 [4 λ [0 1]]] λ [[6 λ [6 λ [1 [0 3]]]] 2]]]]]]'
#     (λa.(λb.a(bb))(λb.a(bb)))(λabc.c(λde.e(λf.da(λg.f(b(λhi.g((λjkl.ljk)ih)))(a(λh.b(λi.gi(hi)))))(f(b(λg.gf))(λg.a(λh.b(λi.h(if)))e)))))
#

sqr2lam() {
  ./compile.sh |
    o/blcdump -nl 2>/dev/null
}

if [ $# -gt 0 ]; then
  printf %s "$*" | sqr2lam
else
  sqr2lam
fi
