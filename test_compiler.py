#!/usr/bin/env python3

from compiler import *

def check_output(srcexpr: SrcExpr, input: str, output: str):
    received_output = exec_srcexpr(srcexpr, input=input, capture=True)
    assert received_output == output

def test_ident():
    ident = SrcRoot(
        SrcBlock([
            SrcApp(SrcVar("print"), SrcVar("input"))
        ])
    )
    check_output(ident, "We love Ohad", "We love Ohad")

def test_hello_world():
    hello = SrcRoot(
        SrcBlock([
            SrcApp(SrcVar("print"), SrcStr("Hello world 🌍"))
        ])
    )
    check_output(hello, "", "Hello world 🌍")

def test_fib():
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
    print_fib = SrcRoot(
        SrcBlock([
            SrcDefine("fib", fib),
            SrcApp(SrcVar("print"),
                SrcApp(SrcVar("nat->str"), SrcApp(SrcVar("fib"), SrcNat(8))))
        ])
    )

    check_output(print_fib, "", "S" * 21)

def test_even_odd():
    even = SrcAbs("n",
        SrcCall(SrcVar("is-zero"), [
            SrcVar("n"),
            SrcBool(True),
            SrcApp(SrcVar("odd"), SrcApp(SrcVar("--"), SrcVar("n")))
        ])
    )
    odd = SrcAbs("n",
        SrcCall(SrcVar("is-zero"), [
            SrcVar("n"),
            SrcBool(False),
            SrcApp(SrcVar("even"), SrcApp(SrcVar("--"), SrcVar("n")))
        ])
    )

    print_even_odd = lambda n: SrcRoot(
            SrcBlock([
                SrcDefine("odd", odd),
                SrcDefine("even", even),
                SrcApp(SrcVar("print"),
                    SrcCall(SrcApp(SrcVar("even"), SrcNat(n)), [
                        SrcStr("even"),
                        SrcStr("odd"),
                    ])
                ),
                SrcApp(SrcVar("print"), SrcStr("\n"))
            ])
        )

    check_output(print_even_odd(151), "", "odd\n")
    check_output(print_even_odd(21), "", "odd\n")
    check_output(print_even_odd(12), "", "even\n")
    check_output(print_even_odd(0), "", "even\n")

def test_even_odd_parse():
    even_odd = '''
(define odd
    (lambda n (if (is-zero n) #f (odd (-- n)))))
(define even
    (lambda n (if (is-zero n) #t (even (-- n)))))
(if (even 8)
    (print "even")
    (print "odd"))
    '''

    check_output(parse(even_odd), "", "even")
