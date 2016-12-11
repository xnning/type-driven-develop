# Predicates: expressing assumptions and contracts in types

## Contents

- Describing and checking membership of a vector using a predicate
- Using predicates to describe contracts for function inputs and outputs
- Reasoning about system state in types

## Notes

- By expressing relationships between data in types, you can be explicit about the assumptions you're making about the inputs to a function, and have those assumptions checked by the type checker when those functions are called.

- Elem type: guaranteeing a value is in a vector

```idris
data Elem : a -> Vect k a -> Type where
     Here : Elem x (x :: xs)
     There : (later : Elem x xs) -> Elem x (y :: xs)

maryInVector : Elem "Mary" ["Peter", "Paul", "Mary"]
maryInVector = There (There Here)
```

- Define removeElem

```idris
removeElem : (value : a) -> (xs : Vect (S n) a)  
          -> (prf : Elem value xs) 
          -> Vect n a
removeElem value (value :: ys) Here = ys
removeElem {n = Z} value (y :: []) (There later) = absurd later
removeElem {n = (S k)} value (y :: ys) (There later)
                                          = y :: removeElem value ys later
```

- absurd: for types are instance of Uninhabited

```idris
absurd : Uninhabited t => (h : t) -> a
absurd h = void (uninhabited h)
```

- Uninhabited: if a type has no value, it can be defined as instance of Uninhabited interface

```idris
interface Uninhabited t where
  uninhabited : t -> Void

Uninhabited (2 + 2 = 5) where
    uninhabited Refl impossible
```

- use auto-implicit argument to let Idris construct the proofs for you:

```idris
removeElem_auto : (value : a) -> (xs : Vect (S n) a) ->
                  {auto prf : Elem value xs} -> Vect n a
removeElem_auto value xs {prf} = removeElem value xs prf
```

- Make the predicate decidable:

```idris
isElem : DecEq ty => (value : ty) -> (xs : Vect n ty) -> Dec (Elem value xs)
```
