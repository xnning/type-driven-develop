module Main

import Data.Vect

infixr 5 .+.
data Schema = SString
            | SInt
            | SChar
            | (.+.) Schema Schema


SchemaType : Schema -> Type
SchemaType SString = String
SchemaType SInt = Int
SchemaType SChar = Char
SchemaType (x .+. y) = (SchemaType x, SchemaType y)

record DataStore where
  constructor MkData
  schema: Schema
  size : Nat
  items : Vect size (SchemaType schema)

addToStore : (store: DataStore) -> (SchemaType (schema store)) -> DataStore
addToStore (MkData schema size items) newitem = MkData _ _ (addToData items)
  where
    addToData : Vect old (SchemaType schema) -> Vect (S old) (SchemaType schema)
    addToData [] = [newitem]
    addToData (x :: xs) =  x :: addToData xs

data Command : Schema -> Type where
       SetSchema : (newschema : Schema) -> Command schema
       Add : SchemaType schema -> Command schema
       Get : Integer -> Command schema
       Quit : Command schema

parseSchema : List String -> Maybe Schema
parseSchema ("String" :: xs) =
  case xs of
      [] => Just SString
      _  => case parseSchema xs of
              Nothing => Nothing
              Just xs_sch => Just (SString .+. xs_sch)
parseSchema ("Int" :: xs) =
  case xs of
      [] => Just SInt
      _  => case parseSchema xs of
              Nothing => Nothing
              Just xs_sch => Just (SInt .+. xs_sch)
parseSchema _ = Nothing

parsePrefix : (schema : Schema) -> (str : String) -> Maybe (SchemaType schema, String)
parsePrefix SString str = getQuoted (unpack str)
  where getQuoted : List Char -> Maybe (String, String)
        getQuoted ('"' :: xs) =
          case span (/= '"') xs of
            (quoted, '"' :: rest) => Just (pack quoted, ltrim (pack rest))
            _ => Nothing
        getQuoted _ = Nothing
parsePrefix SInt str = case span isDigit str of
                         ("", rest) => Nothing
                         (num, rest) => Just (cast num, ltrim rest)
parsePrefix (x .+. y) str = do
    (l_val, input) <- parsePrefix x str
    (r_val, rest) <- parsePrefix y input
    pure ((l_val, r_val), rest)
parseBySchema : (schema : Schema) -> (str : String) -> Maybe (SchemaType schema)
parseBySchema schema str = case (parsePrefix schema str ) of
                                Just (res, "") => Just res
                                _ => Nothing

parseCommand : (schema: Schema) -> String -> String -> Maybe (Command schema)
parseCommand schema "add" str = do
    cmd <- parseBySchema schema str
    Just (Add cmd)
parseCommand schema "get" val = case all isDigit (unpack val) of
                                False => Nothing
                                True => Just (Get (cast val))
parseCommand schema "quit" "" = Just Quit
parseCommand schema "schema" rest = do
    schemaok <- parseSchema (words rest)
    Just (SetSchema schemaok)
parseCommand _ _ _ = Nothing

parse : (schema: Schema) -> (input : String) -> Maybe (Command schema)
parse schema input = case span (/= ' ') input of
                       (cmd, args) =>  parseCommand schema cmd (ltrim args)

display : SchemaType schema -> String
display {schema = SString} item = item
display {schema = SInt} item = show item
display {schema = (x .+. y)} (a, b) = display a ++ ", " ++ display b

getEntry : (pos : Integer) -> (store: DataStore) -> Maybe (String, DataStore)
getEntry pos store = let store_items = items store
                     in case integerToFin pos (size store) of
                     Nothing => Just ("Out of range\n", store)
                     Just id => Just (display (index id store_items) ++ "\n", store)

setSchema : (store : DataStore) -> Schema -> Maybe DataStore
setSchema store schema = case size store of
                           Z => Just (MkData schema _ [])
                           S k => Nothing

processInput : DataStore -> String -> Maybe (String, DataStore)
processInput store inp = case parse (schema store) inp of
                      Nothing => Just ("Invalid command\n", store)
                      Just (Add item) =>
                        Just ("ID: " ++ show (size store) ++ "\n", addToStore store item)
                      Just (SetSchema schema') =>
                        case setSchema store schema' of
                          Nothing => Just ("Can't update schema\n", store)
                          Just store' => Just ("OK\n", store')
                      Just (Get pos) => getEntry pos store
                      Just Quit => Nothing

main : IO ()
main = replWith (MkData SString _ []) "Command: " processInput
