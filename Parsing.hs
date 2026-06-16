{-# LANGUAGE LambdaCase, RankNTypes, ScopedTypeVariables #-}


module Parsing where

import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Perm

import Control.Monad
import Control.Arrow
import Data.Ord
import Data.List
import Data.Ratio
import Data.Maybe
import Data.Either

import Utils
import OperadTree
import Signature
import Measure
import Polynomials
import IO
import PrettyPrinting

import Rewriting
import CriticalPairs


----------------------------


whitespace :: Parser ()
whitespace = skipMany (oneOf " \t")

whitespace_ :: a -> Parser a
whitespace_ x = skipMany (oneOf " \t") >> return x

endOfLine :: Parser ()
endOfLine = (try (string "\n\r") <|> try (string "\r\n") <|> string "\r" <|> string "\n" <?> "end of line") >> return ()

comment :: Parser ()
comment = (string "#" >> many (noneOf "\n\r") >> endOfLine)

emptyLine :: Parser ()
emptyLine = comment <|> (whitespace >> endOfLine)

emptyLines :: Parser ()
emptyLines = skipMany emptyLine


----------------------------

-- Basics

readName :: Parser String
readName = many1 letter

readNum :: (Num a, Read a) => Parser a
readNum = liftM read (many1 digit)

readSign :: Parser Bool
readSign = (char '-' >> return False) <|> return True

----------------------------

-- Parentheses

match :: Char -> Char
match = \case '(' -> ')'; '[' -> ']'; '{' -> '}'

parens :: Parser a -> Parser (Char,a,Char)
parens p = do o <- oneOf "({["
              whitespace
              a <- p
              whitespace
              c <- char (match o)
              return (o,a,c)

----------------------------

-- Rationals

readDiv :: Parser Int
readDiv = oneOf "/%" >> whitespace >> readNum

readRatio :: Parser Scalar
readRatio = do n <- readNum
               whitespace
               d <- readDiv <|> return 1
               return (fromIntegral n % fromIntegral d)

----------------------------

-- Actions

readActions :: Parser (Bool,Bool)
readActions = do string "actions:" >> whitespace
                 permute $ (,) <$?> (False, string "normalise" >> whitespace_ True)
                               <|?> (False, string "count" >> whitespace_ True)

----------------------------

-- Configuration

readCountLimit :: Parser Int
readCountLimit = do string "count limit:" >> whitespace
                    readNum <|> return 0


readOutput :: Parser (Bool,Bool,Bool,Bool)
readOutput = do string "output:" >> whitespace
                permute $ (,,,) <$?> (False, string "initial"    >> whitespace_ True)
                                <|?> (False, string "new"        >> whitespace_ True)
                                <|?> (False, string "final"      >> whitespace_ True)
                                <|?> (False, string "evaluation" >> whitespace_ True)

readTimeLimit :: Parser (Maybe Int)
readTimeLimit = do string "time limit:" >> whitespace
                   liftM Just readNum <|> return Nothing

readArityLimit :: Parser (Maybe Int)
readArityLimit = do string "arity limit:" >> whitespace
                    liftM Just readNum <|> return Nothing

----------------------------

-- Operad type

readOType :: Parser (Bool,Bool)
readOType = do string "operad type:" >> whitespace
               permute $ f <$?> (False, try (string "shuffle"    >> whitespace_ True))
                           <|?> (False,      string "unsigned"   >> whitespace_ True)
                           <|?> (False,      string "asymmetric" >> whitespace_ True)
                           <|?> (False, try (string "signed"     >> whitespace_ True))
            where f a b c d | a, c = error "incompatible options: \"shuffle\", \"asymmetric\""
                            | b, d = error "incompatible options: \"unsigned\", \"signed\""
                            | otherwise = (if d then a else not c, d)

                            


----------------------------

-- Measures

readMeasure :: Parser Measure 
readMeasure = do string "measure:"
                 whitespace
                 ws <- many (readName >>= whitespace_)
                 endOfLine
                 return $ f ws
  where f [] = End
        f (x:xs) | x == "ar" = Ar 0 $ f xs
                 | x == "deg" = Deg [] $ f xs
                 | x == "perm" = Perm [] $ f xs
                 | x == "permr" = PermR [] $ f xs
                 | x == "deglex" = DegLex [] $ f xs
                 | x == "deglexr" = DegLexR [] $ f xs
                 | x == "weighted" = Weighted [] $ f xs
                 | otherwise = error "unrecognised measure"

----------------------------

-- Signatures

readOperator :: Parser Operator 
readOperator = do (n,w,s) <- readOp1
                  whitespace
                  (o,a,c) <- parens (readNum)
                  return $ Op a n w s [o,c]

readOp1 :: Parser (String,Int,Bool)
readOp1 = permute $ (,,) <$?> ("",readName >>= whitespace_)
                         <|?> (0,readNum >>= whitespace_)
                         <|?> (True,char '+' >> whitespace_ False)


readSignature :: Parser Signature
readSignature = string "signature:" >> whitespace >> many (readOperator >>= whitespace_)

----------------------------

readField :: Parser Field
readField = do string "field:"
               whitespace
               (readNum >>= f) <|> (endOfLine >> return Nothing)
                 where f i = if i `elem` [1,2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97]
                                then return (Just i)
                                else fail "only prime integer fields below 100 are supported"

----------------------------

-- Trees

readLeaf :: OperadTree a => Parser a
readLeaf = liftM leaf (readNum <|> (char '*' >> return 0)) 

readZnLeaves :: OperadTree a => Parser a
readZnLeaves = try $ do string "znleaves"
                        whitespace
                        (o,n,c) <- parens readNum
                        if n <= 0
                          then fail "znleaves: number of leaves must be positive"
                          else return $ znleaves n

readVertex :: OperadTree a => Signature -> Parser a
readVertex sig = do n <- try readName <|> return ""
                    whitespace
                    (o,ts,c) <- parens $ many1 (readTree sig >>= whitespace_)
                    case findIndex (\op -> name op == n && bracket op == [o,c]) sig of
                      Just i  -> return $ vertexS i (sgn $ sig !! i) ts
                      Nothing -> error "unknown vertex type"

readTree :: OperadTree a => Signature -> Parser a
readTree sig = readLeaf <|> readVertex sig


----------------------------

-- Polynomials

readMono :: OperadTree a => Signature -> Measure -> Parser (Mono a)
readMono sig m = do x <- readRatio <|> return 1
                    whitespace
                    t <- readVertex sig
                    return (t, measure (weighting sig) t m,x)

readPoly :: OperadTree a => Signature -> Field -> Measure -> Parser (Poly a)
readPoly sig z m = do whitespace
                      s  <- readSign
                      whitespace
                      m0@(x,y,i) <- readMono sig m
                      whitespace
                      p0 <- f
                      return (if s then m0 : p0 else (x,y,neg_ z i) : p0)
  where
    f = ((endOfLine <|> eof) >> return []) <|>
        (do s <- oneOf "+-"
            whitespace
            m@(x,y,i) <- readMono sig m
            whitespace
            p <- f
            return (if s == '+' then m:p else (x,y,neg_ z i) : p))

readPolysBlock :: OperadTree a => String -> Signature -> Field -> Measure -> Parser [Poly a]
readPolysBlock label sig z m = do string label
                                  skipMany space
                                  ps <- many (try (readPoly sig z m) <|> (emptyLine >> return []))
                                  return $ filter (/= []) ps

verifyPolys :: OperadTree a => Bool -> String -> Field -> Signature -> Measure -> Parser [Poly a]
verifyPolys b label z sig m = do
  t <- readPolysBlock label sig z m
  case (if b then verifyS_ sig t else verifyA_ sig t) of
    Just s  -> fail s
    Nothing -> do
      let trees = map (\(tr,_,_) -> tr) (concat t)

      if b && not (all isShuffleTree trees)
        then fail "Input Error: A non-shuffle tree was provided in input.txt while operad type is set to 'shuffle'."
        else case adjustField z t of
               Nothing -> fail "Field adjustment failed"
               Just r  -> return r
                                                           
-- Check if a tree satisfies the shuffle tree condition
isShuffleTree :: OperadTree a => a -> Bool
isShuffleTree t = case splitVertex t of
  Left _        -> True  -- A single leaf is always valid
  Right (ts, _) -> all isShuffleTree ts && isSorted (map minleaf ts)

adjustField :: Field -> [Poly a] -> Maybe [Poly a]
adjustField Nothing  = Just
adjustField (Just i) = mapM (mapM f)
  where f (t,m,x) = if denominator x == 1 then Just (t,m,(numerator x `mod` fromIntegral i) % 1) else Nothing

----------------------------


readConfig :: Parser Config
readConfig = do emptyLines
                (n,g) <- readActions
                emptyLines
                l <- readCountLimit
                emptyLines
                (b,c,d,e) <- readOutput
                emptyLines
                t <- readTimeLimit
                emptyLines
                a <- readArityLimit
                emptyLines
                f <- readField
                emptyLines
                o <- readOType
                emptyLines
                m <- readMeasure
                emptyLines
                s <- liftM verifySig readSignature
                emptyLines
                x <- if fst o then if snd o then liftM (Left  . Right) $ verifyPolys True  "theory:" f s m
                                            else liftM (Left  . Left ) $ verifyPolys True  "theory:" f s m
                              else if snd o then liftM (Right . Right) $ verifyPolys False "theory:" f s m
                                            else liftM (Right . Left ) $ verifyPolys False "theory:" f s m
                emptyLines
                r <- optionMaybe $ try $
                       case x of
                         Left  (Left  _) -> liftM (Left  . Left ) $ verifyPolys True  "reduce:" f s m
                         Left  (Right _) -> liftM (Left  . Right) $ verifyPolys True  "reduce:" f s m
                         Right (Left  _) -> liftM (Right . Left ) $ verifyPolys False "reduce:" f s m
                         Right (Right _) -> liftM (Right . Right) $ verifyPolys False "reduce:" f s m
                emptyLines
                eof
                return (Config n g l a t b c d e f m s x r)

----------------------------


readIn :: String -> IO Config
readIn file = do xs <- readFile file
                 case parse readConfig "" xs of
                   Left err -> error (show err)
                   Right cp -> return cp

----------------------------

