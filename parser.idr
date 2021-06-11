import Data.String
import Data.List

record Parser a where
  constructor MkParser
  parse : String -> List (String, a)

predP : (Char -> Bool) -> Parser Char
predP predicat = MkParser f
 where
   f : String -> List (String, Char)
   f "" = []
   -- f s with (unpack s)
   --   f s | [] = []
   --   f s | (c::cs) = if predicat c then [(pack cs,c)] else []
   f s = case unpack s of
    [] => []
    (c::cs) => if predicat c then [(pack cs,c)] else []

charP : Char -> Parser Char
charP char = predP (\c => c == char)

stringP : String -> Parser String
stringP s = MkParser f
 where
   f : String -> List (String, String)
   f s' = if s == s' then [("",s)] else []

dropS : Nat -> String -> String
dropS i s = pack $ drop i (unpack s)

dropWhileS : String -> (Char -> Bool) -> String
dropWhileS s p = pack $ dropWhile p (unpack s)

skip : (Char -> Bool) -> Parser ()
skip p = MkParser (\s => [(dropWhileS s p, ())])

prefixP : String -> Parser String
prefixP s = MkParser f
 where
   f : String -> List (String, String)
   f inp = if isPrefixOf s inp then [(dropS (length s) inp, s)] else []

Functor Parser where
 map f (MkParser p1) = MkParser p2
  where
  convert : List (String, a) -> List (String, b)
  convert l = map (\(s, val) => (s, f val)) l
  p2 : String -> List (String, b)
  p2 s = convert (p1 s)

applyP : Parser (a -> b) -> Parser a -> Parser b
applyP (MkParser pab) (MkParser pa) = MkParser
 (\s => [(s2,fab a_val) | (s1,fab) <- pab s, (s2,a_val) <- pa s1])
-- applyP (MkParser pab) (MkParser pa) = MkParser f
--  where
--   f : String -> List (String, b)
--   f s = [(s2,fab a_val) | (s1,fab) <- pab s, (s2,a_val) <- pa s1]

Applicative Parser where
 pure x = MkParser (\s => [(s, x)])
 (<*>) = applyP

Alternative Parser where
 -- (<|>) p1 p2 = MkParser (\s => parse p1 s ++ parse p2 s)
 (<|>) (MkParser p1) (MkParser p2) = MkParser \s => p1 s ++ p2 s
 empty = MkParser (const [])

some : Alternative f => f a -> f (List a)
many : Alternative f => f a -> f (List a)
some v = (::) <$> v <*> many v
many v = some v <|> pure []

data Operator = Add | Mul
data Expr = ConstExpr Int | BinaryExpr Expr Operator Expr | NegateExpr Expr

intParser : Parser Int
constParser : Parser Expr
binParser : Parser Expr
exprParser : Parser Expr
negParser : Parser Expr
  
intParser = MkParser $ \s =>
 let
 digitParser = predP isDigit
 res = parse (some digitParser) s
 in
 case res of
  [] => []
  ((q,w) :: xs) => case parseInteger $ pack w of
                        Just v => [(q,v)]
                        Nothing => []

constParser = ConstExpr <$> intParser

exprParser = constParser <|> binParser <|> negParser

negParser = charP '-' *> (NegateExpr <$> exprParser)

binOpParser : Parser Operator
binOpParser = plusParser <|> mulParser
 where
 plusParser : Parser Operator
 mulParser : Parser Operator
 plusParser = charP '+' $> Add
 mulParser = charP '*' $> Mul

binParser = charP '(' *> q <* charP ')'
  where
  q : Parser Expr
  q = BinaryExpr <$> exprParser <*> (charP ' ' *> binOpParser <* charP ' ') <*> exprParser


test1 : List (String, Expr)
test1 = parse exprParser "123"

test2 : List (String, Expr)
test2 = parse exprParser "(123 + 321)"

test3 : List (String, Expr)
test3 = parse exprParser "-(123 + 321)"

test4 : List (String, Expr)
test4 = parse exprParser " -(123 + 321)"
