Plan
====

- Write an interpreter for a dependently typed language
- Possibly JIT compile for faster execution and type checking (since the interpreter will also be used for type-level computations)

Syntax
------

- Function application: `x f`
- Infix operators are whitespace-sensitive: `x+y * z` is `(x + y) * z`
- case is just a zero-arg lambda
