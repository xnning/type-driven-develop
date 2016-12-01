# Interfaces: using constrained generic types

## Contents

- Constraining generic types using interfaces
- Implementing interfaces for specific contexts
- Using interfaces defined in the Prelude

## Notes

- Interfaces in Idris are similar to type classes in Haskell, with some differences:
    - interfaces can be parameterized by values of any type, and are not limited to types or type constructors.
    - interfaces can have multiple implementations.

- Interfaces are limited to names introduced by either a data or record declaration, or primitive types.

- Interfaces in Idris can have any number of parameters, including zero. For example, interface Cast has two parameters.
