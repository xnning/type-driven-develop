-- 9.1.6

data Elem : (x : a) -> (xs : List a) -> Type where
  Here : Elem x (x :: xs)
  There : Elem x xs -> Elem x (y :: xs)

data Last : List a -> a -> Type where
  LastOne : Last [value] value
  LastCons : (prf : Last xs value) -> Last (x :: xs) value

notLast : (neq : (x = value) -> Void) -> Last [x] value -> Void
notLast neq LastOne = neq Refl
notLast _ (LastCons LastOne) impossible
notLast _ (LastCons (LastCons _)) impossible

notInNil : Last [] value -> Void
notInNil LastOne impossible
notInNil (LastCons _) impossible

notInTail : (notLast : Last (y :: xs) value -> Void) -> Last (x :: (y :: xs)) value -> Void
notInTail notLast (LastCons prf) = notLast prf

isLast : DecEq a => (xs : List a) -> (value : a) -> Dec (Last xs value)
isLast [] value = No notInNil
isLast (x :: []) value = case decEq x value of
                           Yes Refl => Yes LastOne
                           No neq => No (notLast neq)
isLast (x :: (y :: xs)) value = case isLast (y :: xs) value of
                                  Yes prf => Yes (LastCons prf)
                                  No notLast => No (notInTail notLast)
