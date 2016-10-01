# Getting Started with Idris

## Contents

- Using built-in types and functions
- Defining Functions
- Structuring Idris programs

## Notes

- Other than language features specific to Idris, comparing to Haskell, the most important difference is that Idris doesn't use lazy evaluation by default.

- Basic types
  - numeric types
    - Int. fixed-width signed integer.
    - Integer. unbound signed integer.
    - Nat. unbound unsigned integer.
    - Double. double precision floating point type.
  - chars and strings
    - Char.
    - String.
  - Boolean.

- `cast` converts types. Idris supports casting between all of the primitive types, and it is possible to add user defined casts.

- Documentation comments `:doc` are used to provide documentation for functions and types at the REPL; introduced with three vertical bars, `|||`
