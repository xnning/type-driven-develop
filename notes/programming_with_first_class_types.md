# Programming with First Class Types

## Contents

- Programming with type level functions
- Writing functions with varying numbers of arguments
- Using type level functions to calculate the structure of data
- Refining larger interactive programs

## Notes

- type synonyms

```idris
Position : Type
Position = (Double, Double)
```

- type-level function: ordinary functions that happen to return a Type, with a couple of technical differences:
  - type-level functions exist at compile time only.
  - only functions that are total will be evaluated at the type level. Functions that are not total are treated as constants at type level and don't evaluate further.

```idris
StringOrInt : Bool -> Type
StringOrInt False = String
StringOrInt True = Int
```

- Could directly use complex expressions like case in type-level instead of a separate function.

- Calculate variable numbers of arguments

```idris
AdderType : (numargs : Nat) -> Type
AdderType Z = Int
AdderType (S k) = (next : Int) -> AdderType k
```
