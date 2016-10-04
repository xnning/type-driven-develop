import Data.Vect as V

-- 4.1.5 Exercises
data Tree elem = Empty
  | Node (Tree elem) elem (Tree elem)

%name Tree tree, tree1

insert : Ord elem => elem -> Tree elem -> Tree elem
insert x Empty = Node Empty x Empty
insert x (Node left val right)
  = case compare x val of
      LT => Node (insert x left) val right
      EQ => Node left val right
      GT => Node left val (insert x right)

listToTree : Ord a => List a -> Tree a
listToTree [] = Empty
listToTree (x :: xs) = insert x (listToTree xs  )

treeToList : Tree a -> List a
treeToList Empty = []
treeToList (Node tree x tree1) = treeToList tree ++ [x] ++ treeToList tree1

data Expr = Lit Integer
          | Add Expr Expr
          | Sub Expr Expr
          | Mul Expr Expr

eval : Expr -> Integer
eval (Lit x) = x
eval (Add x y) = eval x + (eval y)
eval (Sub x y) = eval x - (eval y)
eval (Mul x y) = eval x * (eval y)

maxMaybe : Ord a => Maybe a -> Maybe a -> Maybe a
maxMaybe Nothing y = y
maxMaybe x Nothing = x
maxMaybe jx@(Just x) jy@(Just y) = if x > y then jx else jy

data Shape = Triangle Double Double
  | Rectangle Double Double
  | Circle Double

area : Shape -> Double
area (Triangle base height) = 0.5 * base * height
area (Rectangle length height) = length * height
area (Circle radius) = pi * radius * radius

data Picture = Primitive Shape
  | Combine Picture Picture
  | Rotate Double Picture
  | Translate Double Double Picture

biggestTriangle : Picture -> Maybe Double
biggestTriangle (Primitive t@(Triangle x y)) = Just (area t)
biggestTriangle (Primitive _) = Nothing
biggestTriangle (Combine x y) = maxMaybe (biggestTriangle x) (biggestTriangle y)
biggestTriangle (Rotate _ y) = biggestTriangle y
biggestTriangle (Translate _ _ z) = biggestTriangle z

data Vect' : Nat -> Type -> Type where
  Nil : Vect' Z a
  (::) : (x : a) -> (xs : Vect' k a) -> Vect' (S k) a

%name Vect' xs, ys, zs

append : Vect' n elem -> Vect' m elem -> Vect' (n + m) elem
append [] ys = ys
append (x :: xs) ys = x :: (append xs ys)

zip : Vect' n a -> Vect' n b -> Vect' n (a, b)
zip [] [] = []
zip (x :: xs) (y :: ys) = (x, y) :: zip xs ys

-- 4.2.4 Exercises

data PowerSource = Petrol | Pedal | Electric
data Vehicle : PowerSource -> Type where
  Bicycle : Vehicle Pedal
  Car : (fuel : Nat) -> Vehicle Petrol
  Bus : (fuel : Nat) -> Vehicle Petrol
  Unicycle : Vehicle Pedal
  Motorcycle: (fuel : Nat) -> Vehicle Petrol
  Trams : Vehicle Electric

wheels : Vehicle power -> Nat
wheels Bicycle = 2
wheels (Car fuel) = 4
wheels (Bus fuel) = 4
wheels Unicycle = 1
wheels (Motorcycle fuel) = 2
wheels Trams = 4

refuel : Vehicle Petrol -> Vehicle Petrol
refuel (Car fuel) = Car 100
refuel (Bus fuel) = Bus 200
refuel (Motorcycle fuel) = Motorcycle 80

take: (n : Nat) -> Vect' (n + m) a -> Vect' n a
take Z xs = []
take (S k) (x :: xs) = x :: take k xs

sumEntries : Num a => (pos: Integer) -> Vect n a -> Vect n a -> Maybe a
sumEntries {n} pos xs ys = case integerToFin pos n of
  Nothing => Nothing
  Just idx => Just ((index idx xs) + (index idx ys))
