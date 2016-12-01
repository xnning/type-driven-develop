-- 7.1.6

data Shape = Triangle Double Double
           | Rectangle Double Double
           | Circle Double

Eq Shape where
    (==) (Triangle x z) (Triangle x2 z2) = x == x2 && z == z2
    (==) (Rectangle x z) (Rectangle x2 z2) = x == x2 && z == z2
    (==) (Circle x) (Circle x2) = x == x2
    (==) _ _ = False

area : Shape -> Double
area (Triangle base height) = 0.5 * base * height
area (Rectangle length height) = length * height
area (Circle radius) = pi * radius * radius

Ord Shape where
  compare x y = compare (area x) (area y)

-- 7.2.4

data Expr num = Val num
              | Add (Expr num) (Expr num)
              | Sub (Expr num) (Expr num)
              | Mul (Expr num) (Expr num)
              | Div (Expr num) (Expr num)
              | Abs (Expr num)

eval : (Neg num, Integral num) => Expr num -> num
eval (Val x) = x
eval (Add x y) = eval x + eval y
eval (Sub x y) = eval x - eval y
eval (Mul x y) = eval x * eval y
eval (Div x y) = eval x `div` eval y
eval (Abs x) = abs (eval x)

Num ty => Num (Expr ty) where
    (+) = Add
    (*) = Mul
    fromInteger = Val . fromInteger

Neg ty => Neg (Expr ty) where
    negate x = 0 - x
    (-) = Sub
    abs = Abs

(Show num) => Show (Expr num) where
    show (Val x) = show x
    show (Add x y) = "(" ++ show x ++ " + " ++ show y ++ ")"
    show (Sub x y) = "(" ++ show x ++ " - " ++ show y ++ ")"
    show (Mul x y) = "(" ++ show x ++ " * " ++ show y ++ ")"
    show (Div x y) = "(" ++ show x ++ " / " ++ show y ++ ")"
    show (Abs x) = "abs " ++ show x

(Neg num, Integral num, Eq num) => Eq (Expr num) where
    (==) x y = eval x == eval y

(Neg num, Integral num) => Cast (Expr num) num where
    cast = eval

-- 7.3.4

Functor Expr where
    map func (Val x) = Val (func x)
    map func (Add x y) = Add (map func x) (map func y)
    map func (Sub x y) = Sub (map func x) (map func y)
    map func (Mul x y) = Mul (map func x) (map func y)
    map func (Div x y) = Div (map func x) (map func y)
    map func (Abs x) = Abs (map func x)

data Vect: Nat -> Type -> Type where
    Nil : Vect Z a
    (::) : (x : a) -> (xs: Vect k a) -> Vect (S k) a

%name Vect xs, ys, zs

Eq a => Eq (Vect len a) where
    (==) [] [] = True
    (==) (x :: xs) (y :: ys) = x == y && xs == ys

Foldable (Vect len) where
    foldr func init [] = init
    foldr func init (x :: xs) = func x (foldr func init xs)
