Brainfuck
=========

This is a README that describes the project.




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
