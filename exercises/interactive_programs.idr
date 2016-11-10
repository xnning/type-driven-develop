import System
import Data.Vect

-- 5.1.4
printLonger : IO ()
printLonger = do str1 <- getLine
                 str2 <- getLine
                 if length str1 > length str2
                 then putStrLn (show (length str1))
                 else putStrLn (show (length str2))

printLonger2 : IO ()
printLonger2 = getLine >>= \str1 =>
              getLine >>= \str2 =>
              if length str1 > length str2
              then putStrLn (show (length str1))
              else putStrLn (show (length str2))

-- 5.2.4

-- 1
readNumber : IO (Maybe Nat)
readNumber = do input <- getLine
                if all isDigit (unpack input)
                then pure (Just (cast input))
                else pure Nothing

guess : (target : Nat) -> IO ()
guess target = do putStrLn "enter a number"
                  Just num <- readNumber | Nothing => guess target
                  if num > target
                  then do putStrLn "too high"
                          guess target
                  else if num < target
                       then do putStrLn "too low"
                               guess target
                  else putStrLn "you are right!"

-- 2

main' : IO ()
main' = do num <- time
           let target = (num `mod` 100) + 1
           guess (cast target)

-- 3
guess2 : (target : Nat) -> (guesses: Nat) -> IO ()
guess2 target guesses = do putStrLn ("guess time: " ++ (show guesses))
                           putStrLn "enter a number"
                           Just num <- readNumber | Nothing => guess target
                           if num > target
                           then do putStrLn "too high"
                                   guess2 target (guesses + 1)
                           else if num < target
                                then do putStrLn "too low"
                                        guess2 target (guesses + 1)
                                else putStrLn "you are right!"

-- 4
repl2 : String -> (String -> String) -> IO ()
repl2 prompt f = do putStr prompt
                    str <- getLine
                    putStr (f str)
                    repl2 prompt f

replWith2 : (state: a) -> String -> (a -> String -> Maybe (String, a)) -> IO ()
replWith2 state prompt f = do putStr prompt
                              str <- getLine
                              case (f state str) of
                                Just (out, newstate) => do putStr out
                                                           replWith newstate prompt f
                                Nothing => pure ()

-- 5.3.5

readToBlank : IO (List String)
readToBlank = do x <- getLine
                 if x == "" then pure []
                 else do xs <- readToBlank
                         pure (x :: xs)

readAndSave : IO ()
readAndSave = do putStrLn "Enter content (blank line to end):"
                 content <- readToBlank
                 putStrLn "Input file name:"
                 filename <- getLine
                 Right () <- writeFile filename (unlines content)
                     | Left err => putStrLn (show err)
                 pure ()

readVectFile : (filename : String) -> IO (n ** Vect n String)
readVectFile filename = do Right file <- openFile filename Read
                             | Left _ => pure (_ ** [])
                           Right context <- readContent file
                             | Left _ => pure (_ ** [])
                           closeFile file
                           pure context
  where readContent : (file: File) -> IO (Either FileError (n ** Vect n String))
        readContent file = do eof <- fEOF file
                              if eof
                              then pure (Right (_ ** []))
                              else do Right line <- fGetLine file
                                        | Left err => pure (Left err)
                                      Right (_ ** lines) <- readContent file
                                        | Left err => pure (Left err)
                                      pure (Right (_ ** line :: lines))
