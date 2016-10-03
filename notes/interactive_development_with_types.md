# Interactive Development with Types

## Contents

- Defining functions by pattern match
- Type-driven interactive editing in Atom
- Adding precision to function types
- Practical programming with vectors

## Notes

- interactive editing
  - Adding definitions: Given a type declaration, Idris can add a skeleton definition of a function which satisfies that type.
  - Case analysis: Given a skeleton function definition, with arguments, Idris can use the type of those arguments to help define the function by pattern matching.
  - Expression search: Given a hole, with a precise enough type, Idris can try to find an expression which satifies the hole's type, refining the definition.

- bound implicits:
  - For clarity and readability, it can be useful to give explicit types to implicit arguments.
  - If there is a dependency between an implicit argument and some other argument, we may need to use a bound implicit to make this clear to Idris.

- implicit arguments:
  - `{n}` in a pattern brings the implicit argument n into scope, allowing us to use it directly.
  - `{n = value}` give explicit values for implicit arguments in application.
  - `{n = value}` can also be used on the left hand side of a definition, to pattern match on an implicit argument.
