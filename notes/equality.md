# Equality: expressing relationships between data

## Contents

- Expressing properties of functions and data
- Checking and guaranteeing equalities between data
- Showing when cases are impossible with the empty type Void

## Notes

**Equality**

- To express values in type level are identical, for example two vectors have the same length, you will need to create a more precise type for the equality test, where the type guarantees that a comparison between two inputs can only be successful if the inputs really are identical. For example, two nats are equal:

```idris
data EqNat : (num1 : Nat) -> (num2 : Nat) -> Type where
   Same : (num : Nat) -> EqNat num num

checkEqNat : (num1 : Nat) -> (num2 : Nat) -> Maybe (EqNat num1 num2)
checkEqNat Z Z = Just (Same Z)
checkEqNat Z (S k) = Nothing
checkEqNat (S k) Z = Nothing
checkEqNat (S k) (S j) = do Same s <- checkEqNat k j
                            pure (Same (S s))
```

- Now, we could implement exactLength

```idris
exactLength : (len : Nat) -> (input : Vect m a) -> Maybe (Vect len a)
exactLength {m} len input = case checkEqNat m len of
                                 Nothing => Nothing
                                 Just (Same m) => Just input
```

- Rather than defining a specific equality type and function for every possible type, Idris provides a generic equality type. Conceptually,

```idris
data (=) : a -> b -> Type where
   Refl : x = x

-- then checkEqNat could be defined as

checkEqNat : (num1 : Nat) -> (num2 : Nat) -> Maybe (num1 = num2)
checkEqNat Z Z = Just Refl
checkEqNat Z (S k) = Nothing
checkEqNat (S k) Z = Nothing
checkEqNat (S k) (S j) = case checkEqNat k j of
                              Nothing => Nothing
                              -- cong : {func : a -> b} -> x = y -> func x = func y
                              Just prf => Just (cong prf)
```

**Rewrite**

- rewrite a proof on the type of expression

```idris
myReverse : Vect n elem -> Vect n elem
myReverse [] = []
myReverse {n = S k} (x :: xs)
        = let result = myReverse xs ++ [x] in
              rewrite plusCommutative 1 k i in result
```

**Impossible**

- To express something is impossible, we use the Void

```idris
data Void : Type where

twoPlusTwoNotFive : 2 + 2 = 5 -> Void
twoPlusTwoNotFive Refl impossible
```

- To State a property is decidable (either we have the proof or it is impossible), we use the Dec

```idris
data Dec : (prop : Type) -> Type where
     Yes : (prf : prop) -> Dec prop
     No  : (contra : prop -> Void) -> Dec prop

interface DecEq ty where
    decEq : (val1 : ty) -> (val2 : ty) -> Dec (val1 = val2)
```
