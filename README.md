Brainfuck
=========

This is a project where I try to formalize
[brainfuck](http://en.wikipedia.org/wiki/Brainfuck) in
[Coq](http://en.wikipedia.org/wiki/Coq).

Goal
---

The goal is to prove properties about brainfuck. I have implemented a compiler
from simple arithmetic expressions (addition, subtraction and multiplication) to
brainfuck. This is done by compiling to a stack machine subset of brainfuck.

Arithmetic expression compiler
------------------------------

A compiler from simple arithmetic expressions with addition, subtraction and
multiplication to brainfuck is included in `ae_compiler.v`. The correctness of
the compiler is proven as well. The idea in the proof is to develop a number of
stack primitives and show their correctness, and then compile down to those
stack primitives.

The hello world example
-----------------------

A `"Hello World!"` example is included in `bf_theorems.v`. It proves that the
given `"Hello World!"` program does output the string `Hello World!` (or rather
the ASCII values corresponding to said string - you have to verify that
yourself!). The proof is largely automated. Unfortunately it takes a while to
finish so it is recommended to comment out the theorem.

The time it takes to compile with the `hello_world` theorem:

    real    0m14.674s
    user    0m14.340s
    sys     0m0.230s

And when `hello_world` is commented out:

    real    0m2.485s
    user    0m2.313s
    sys     0m0.113s

The project's [Github page](https://github.com/reynir/Brainfuck/).
