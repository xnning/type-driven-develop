module Main

import Data.Vect

data DataStore : Type where
  MkData : (size : Nat) -> (items : Vect size String) -> DataStore

size : DataStore -> Nat
size (MkData size' items') = size'

items : (store : DataStore) -> Vect (size store) String
items (MkData size' items') = items'

addToStore : DataStore -> String -> DataStore
addToStore (MkData size items) newitem = MkData _ (addToData items)
  where
    addToData : Vect old String -> Vect (S old) String
    addToData [] = [newitem]
    addToData (x :: xs) =  x :: addToData xs

data Command = Add String
             | Get Integer
             | Quit
             | Size
             | Search String

parseCommand : List String -> Maybe Command
parseCommand ("add" :: str) = Just (Add (unwords str))
parseCommand ["get", val] = case all isDigit (unpack val) of
                            False => Nothing
                            True => Just (Get (cast val))
parseCommand ["quit"] = Just Quit
parseCommand ["size"] = Just Size
parseCommand ["search", str] = Just (Search str)
parseCommand _ = Nothing


parse : (input : String) -> Maybe Command
parse input = parseCommand (words input)

getEntry : (pos : Integer) -> (store: DataStore) -> Maybe (String, DataStore)
getEntry pos store = let store_items = items store
                     in case integerToFin pos (size store) of
                          Nothing => Just ("Out of range\n", store)
                          Just id => Just (index id store_items ++ "\n", store)

search_string : (n: Nat) -> (str:String) -> (store:Vect m String) -> String
search_string n str [] = ""
search_string n str (x :: xs) =
  let rest = search_string (n + 1) str xs
  in case isInfixOf str x of
        True => show n ++ ": " ++ x ++ "\n" ++ rest
        False => rest

processInput : DataStore -> String -> Maybe (String, DataStore)
processInput store inp = case parse inp of
                      Nothing => Just ("Invalid command\n", store)
                      Just (Add item) =>
                        Just ("ID: " ++ show (size store) ++ "\n", addToStore store item)
                      Just (Get pos) => getEntry pos store
                      Just Size => Just ("Current Size: " ++ show (size store) ++ "\n", store)
                      Just (Search str) => Just (search_string 0 str (items store), store)
                      Just Quit => Nothing

main : IO ()
main = replWith (MkData _ []) "Command: " processInput
