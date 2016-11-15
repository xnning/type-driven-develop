import Data.Vect

-- 6.2.3

-- 1

Matrix : Nat -> Nat -> Type
Matrix n m = Vect n (Vect m Int)

testMatrix : Matrix 2 3
testMatrix = [[0, 0, 0], [0, 0, 0]]

-- 2

data Format = Number Format
            | Str Format
            | Lit String Format
            | Ch Format
            | Db Format
            | End

PrintfType : Format -> Type
PrintfType (Number x) = (i: Int) -> PrintfType x
PrintfType (Ch x) = (c: Char) -> PrintfType x
PrintfType (Db x) = (d: Double) -> PrintfType x
PrintfType (Str x) = (s: String) -> PrintfType x
PrintfType (Lit x y) = PrintfType y
PrintfType End = String

printFmt : (fmt: Format) -> (acc : String) -> PrintfType fmt
printFmt (Number x) acc = \i:Int => printFmt x (acc ++ show i)
printFmt (Str x) acc = \s:String => printFmt x (acc ++ s)
printFmt (Lit x y) acc = printFmt y (acc ++ x)
printFmt (Ch x) acc = \c:Char => printFmt x (acc ++ show c)
printFmt (Db x) acc = \d:Double => printFmt x (acc ++ show d)
printFmt End acc = acc

toFormat : (xs: List Char) -> Format
toFormat [] = End
toFormat ('%' :: 'd' :: chars) = Number (toFormat chars)
toFormat ('%' :: 's' :: chars) = Str (toFormat chars)
toFormat ('%' :: 'c' :: chars) = Ch (toFormat chars)
toFormat ('%' :: 'f' :: chars) = Db (toFormat chars)
toFormat ('%' :: chars) = Lit "%" (toFormat chars)
toFormat (c :: chars) = case (toFormat chars) of
                             (Lit x y) => Lit (strCons c x) y
                             others => Lit (cast c) others

printf : (fmt: String) -> PrintfType (toFormat (unpack fmt))
printf fmt = printFmt _ ""

-- 3

TupleVect : (n : Nat) -> (t : Type) -> Type
TupleVect Z t = ()
TupleVect (S k) t = (t, TupleVect k t)

test : TupleVect 4 Nat
test = (1, 2, 3, 4, ())
