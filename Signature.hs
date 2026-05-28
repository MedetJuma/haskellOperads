{-# LANGUAGE LambdaCase #-}

module Signature where

import Data.List

import Utils


------------------------- Operators


data Operator  = Op { arityOP :: Int, 
                      name    :: String,
                      wgt     :: Int,
                      sgn     :: Bool,
                      bracket :: String }
                 deriving (Eq,Ord)

instance Arity Operator where
  arity = arityOP

instance Show Operator where
  show (Op i n w s [o,c]) = (if s then "" else "+") ++ (if w == 0 then "" else show w) ++ n ++ [o] ++ show i ++ [c]


------------------------- Signatures


type Signature = [Operator]

type Weighting = Int -> Int

open :: String -> Char
open [o,_] = o

close :: String -> Char
close [_,c] = c

weighting :: Signature -> Weighting
weighting sig i = let n = length sig in if i < n then wgt (sig !! i) else 0


------------------------- Creating signatures


allTheNames = "" : [ i:n | n <- allTheNames, i <- ['a'..'z']]

makeSig :: [Int] -> Signature
makeSig xs = zipWith5 Op xs ("":"":allTheNames) (repeat 0) (repeat True) ("()" : "[]" : "{}" : repeat "()")

defaultSig = makeSig [2,3,2]

 