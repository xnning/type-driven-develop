-- 1
-- (String, String, String)
-- List String
-- ((Char, String), Char)

-- 2
palindrome : String -> Bool
palindrome s = reverse s == s

-- 3
palindrome2 : String -> Bool
palindrome2 s = let s2 = toLower s in reverse s2 == s2

-- 4
palindrome3 : String -> Bool
palindrome3 s = let s2 = toLower s in
                length s > 10 && reverse s2 == s2

-- 5
palindrome4 : Nat -> String -> Bool
palindrome4 l s = let s2 = toLower s in
                  length s > l && reverse s2 == s2

-- 6
counts : String -> (Nat, Nat)
counts s = (length (words s), length s)

-- 7
top_ten : Ord a => List a -> List a
top_ten l = take 10 (sort l)

-- 8
over_length : Nat -> List String -> Nat
over_length n l = length (filter (\s => length s > n) l)

-- 9
main : IO ()
main = repl "input a string to see whether it is palindrome: "
            (\x => show (palindrome2 x) ++ "\n")
