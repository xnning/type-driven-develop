# Interactive Programs

## Contents

- Writing interactive console programs
- Distinguish evaluation and execution
- Validating user inputs to dependently typed functions

## Notes

- The prelude provides a generic type, IO, which allows us to describe interactive programs which return a value. Functions which return an IO type are still considered pure, because they merely describe interactive actions.

- Totality checking is based on evaluation, not execution. The result of totality checking an IO program therefore tells you whether Idris will produce a finite sequence of actions, but nothing about the behaviour of those action.
