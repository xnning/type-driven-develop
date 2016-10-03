import Data.Vect

create_empties : Vect n (Vect 0 elem)
create_empties = replicate _ []

transpose_helper : (x : Vect n elem) -> (xs_trans : Vect n (Vect k elem)) -> Vect n (Vect (S k) elem)
transpose_helper = zipWith (::)

transpose_mat : Vect m (Vect n elem) -> Vect n (Vect m elem)
transpose_mat [] = create_empties
transpose_mat (x :: xs) = let xs_trans = transpose_mat xs
                          in (transpose_helper x xs_trans)

addMatrix : Num a => Vect n (Vect m a) -> Vect n (Vect m a) -> Vect n (Vect m a)
addMatrix [] [] = []
addMatrix (x :: xs) (y :: ys) = zipWith (+) x y :: addMatrix xs ys

multHelper : Num a => (xs : Vect n (Vect m a)) -> (ys : Vect p (Vect m a)) -> Vect n (Vect p a)
multHelper [] ys = []
multHelper (x :: xs) ys = map (sum . zipWith (*) x) ys :: multHelper xs ys

multMatrix : Num a => Vect n (Vect m a) -> Vect m (Vect p a) -> Vect n (Vect p a)
multMatrix xs ys = multHelper xs (transpose_mat ys)
