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
