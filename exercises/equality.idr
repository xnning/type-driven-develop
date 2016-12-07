 -- 8.1.7

same_cons : {xs: List a} -> {ys: List a} ->
            xs = ys -> x :: xs = x :: ys
same_cons Refl = Refl

same_lists : {xs : List a} -> {ys : List a} ->
             x = y -> xs = ys -> x :: xs = y :: ys
same_lists Refl Refl = Refl

data ThreeEq : a -> b -> c -> Type where
  Refl3 : ThreeEq a a a

allSameS : (x, y, z : Nat) -> ThreeEq x y z -> ThreeEq (S x) (S y) (S z)
allSameS z z z Refl3 = Refl3

-- 8.2.6

myPlusCommutes : (n : Nat) -> (m : Nat) -> n + m = m + n
myPlusCommutes Z m = sym (plusZeroRightNeutral m)
myPlusCommutes (S k) m = rewrite myPlusCommutes k m in plusSuccRightSucc m k

data Vect : Nat -> Type -> Type where
  Nil : Vect Z a
  (::) : a -> Vect k a -> Vect (S k) a

myReverse : Vect n a -> Vect n a
myReverse xs = reverse' [] xs
    where reverse' : Vect n a -> Vect m a -> Vect (n+m) a
          reverse' {n} acc [] = rewrite plusZeroRightNeutral n in acc
          reverse' {n} {m=S k} acc (x :: xs)
            = rewrite sym (plusSuccRightSucc n k) in  reverse' (x::acc) xs

-- 8.3.4

headUnequal : DecEq a => {xs : Vect n a} -> {ys : Vect n a} ->
              (contra : (x = y) -> Void) ->
              ((x :: xs) = (y :: ys)) ->
              Void
headUnequal contra Refl = contra Refl

tailUnequal : DecEq a => {xs : Vect n a} -> {ys : Vect n a} ->
              (contra : (xs = ys) -> Void) ->
              ((x :: xs) = (y :: ys)) ->
              Void
tailUnequal contra Refl = contra Refl

DecEq a => DecEq (Vect n a) where
    decEq [] [] = Yes Refl
    decEq (x :: y) (z :: w) =
      case decEq x z of
        Yes Refl => case decEq y w of
                     Yes Refl => Yes Refl
                     No contra => No (tailUnequal contra)
        No contra => No (headUnequal contra)
