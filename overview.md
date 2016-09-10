#Overview

## Contents

- Getting started with Idris
- An introduction to type-driven development
- The essence of pure functional programming

## Notes

- Type-driven development: we put the type first, treating it as a plan for a program, and use the compiler and type checker as our assistant, guiding us to a complete and working program which satisfies the type.

- two distinct features:
  - In Idris, types are a first-class language construct. A first-class language construct is one for which there are no syntactic restrictions on where or how it can be used.
  - Idris functions themselves can contain holes. A function with a hole is incomplete. Only a value of an appropriate type will fit into the hole.

- Type has type Type 1, then Type 1 has type Type 2, and so on.

