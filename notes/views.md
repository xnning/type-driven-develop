# Views

## Contents

- Defining views, which describe alternative forms of pattern matching
- Introducing the *with* construct for working with views
- Describing efficient traversals of data structures
- Hiding the representation of data behind views

## Notes

- Use views to extend the forms of patterns. ListLast is a view of List.

```idris
data ListLast : List a -> Type where
     Empty : ListLast []
     NonEmpty : (xs : List a) -> (x : a) -> ListLast (xs ++ [x])
```

- Covering function convert original data type into the view form

```idris
total
listLast : (xs : List a) -> ListLast xs
listLast [] = Empty
listLast (x :: xs) = case listLast xs of
                          Empty => NonEmpty [] x
                          NonEmpty ys y => NonEmpty (x :: ys) y
```

- Use `with` block to add a extra arguments to the left hand side of definition.

```idris
describeListEnd : List Int -> String
describeListEnd input with (listLast input)
  describeListEnd [] | Empty = "Empty"
  describeListEnd (xs ++ [x]) | (NonEmpty xs x)
          = "Non-empty, initial portion = " ++ show xs
```

- Valid pattern in Idris:
    - The pattern consists of a data constructor applied to some arguments. The arguments must also be valid patterns.
    - The value of the pattern is forced by some other valid pattern.

**Recursive Views**

- In previous implementation, such as in describeListEnd, each recursive call will rebuild the view, which is inefficient and cause Idris to not be able to tell the totality. So we need recursive views:

```idris
data SnocList : List a -> Type where
     Empty : SnocList []
     Snoc : (rec : SnocList xs) -> SnocList (xs ++ [x])
     
myReverseHelper : (input : List a) -> SnocList input -> List a
myReverseHelper [] Empty = []
myReverseHelper (xs ++ [x]) (Snoc rec) = x :: myReverseHelper xs rec

myReverse : List a -> List a
myReverse xs = myReverseHelper xs (snocList xs)
```

- To use the `with` to make code concise, we need to pass the view directly to avoid rebuild

```idris
myReverse' : List a -> List a
myReverse' xs with (snocList xs)
  myReverse' [] | Empty = []
  myReverse' (ys ++ [x]) | (Snoc rec) = x :: myReverse' ys | rec
```

**Modules**

- Export modifiers, default private:
    - `private`: meaning that the name is not exported at all.
    - `export` : meaning that the name and type are exported, but not the definition.
    - `public export`: meaning that the name, type, and complete definition are exported.

