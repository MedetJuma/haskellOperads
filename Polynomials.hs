{-# LANGUAGE LambdaCase, FlexibleInstances, TypeSynonymInstances #-}

module Polynomials where

import Data.Ord
import Data.List
import Data.Maybe
import Data.Ratio

import Utils
import Signature
import OperadTree
import Measure

-------------------------

-- Monomials

type Field  = Maybe Integer

type Scalar = Ratio Integer

sign :: Field -> Sign -> Scalar
sign Nothing  b = if b then 1 else -1
sign (Just i) b = if b then 1 else (i-1)%1

type Mono a = (a,Measure,Scalar)

isZeroMono  (_,_,i) = i == 0
measureMono (_,y,_) = y
fromMono    (x,_,_) = x

instance Arity a => Arity (Mono a) where
  arity (x,_,_) = arity x

-------------------------

-- Arithmetic for scalar fields

add_ :: Field -> Scalar -> Scalar -> Scalar
add_ Nothing a b = a + b
add_ (Just i) a b = (numerator a + numerator b) `mod` i % 1

mul_ :: Field -> Scalar -> Scalar -> Scalar
mul_ Nothing  a b = a * b
mul_ (Just i) a b = (numerator a * numerator b) `mod` i % 1

div_ :: Field -> Scalar -> Scalar -> Scalar
div_ Nothing  a b = a / b
div_ (Just i) a b | x == 0 = 0
                  | y == 0 = error "division by zero"
                  | otherwise = (x * f 0 1 i y) `mod` i % 1 
                  where x = numerator a
                        y = numerator b
                        f x _ _ 0 = x
                        f x y a b = let (q,r) = quotRem a b in f y (x-y*q) b r

neg_ :: Field -> Scalar -> Scalar
neg_ Nothing  a = - a
neg_ (Just i) a = (- numerator a) `mod` i % 1

-------------------------

-- Polynomials

type Poly a = [Mono a]

-- Take a polynomial to canonical form
--   canonical <ord> <poly>
-- 1) sorts <poly> according to <ord>, largest to smallest
-- 2) sums scalars for equal trees (now adjacent), removes 0-entries
-- 3) normalises scalars to obtain value -1 for the largest element

canonical :: Eq a => Field -> Poly a -> Poly a
canonical z = g . filter (not . isZeroMono) . f . sortBy (flip $ comparing measureMono)
  where f [] = []
        f [x] = [x]
        f ( x@(t,m,a) : xs@((s,n,b) : ys)) = if t == s then f $ (t,m,add_ z a b) : ys else x : f xs
        g [] = []
        g ((x,y,r):xs) = (x,y,1) : map (\(x,y,i) -> (x,y,div_ z i r)) xs
        

-- Verifying signature and tree integrity

verifySig :: Signature -> Signature
verifySig sig = let ns = filter (/="") $ map name sig in if ns == nub ns then sig else error "duplicate name in signature"

verifyArity :: OperadTree a => Signature -> a -> Maybe String
verifyArity sig t = case splitVertex t of 
  Left _ -> Nothing
  Right (ts,_) -> case vertexType t of Just i -> if i >= length sig 
                                                   then Just "vertex type not in signature (this should not happen)"
                                                   else if arity (sig !! i) == length ts
                                                          then listToMaybe $ mapMaybe (verifyArity sig) ts
                                                          else Just ("occurrence of vertex type " ++ show (sig !! i)
                                                                       ++ " with arity " ++ show (length ts) )

verifyShuffle :: OperadTree a => a -> Maybe String
verifyShuffle t = if sort (leaves t) `isPrefixOf` [1..] then Nothing else Just "gap in leaf order, or duplicate leaves"

verifyAsymPoly :: OperadTree a => Signature -> Poly a -> Maybe String
verifyAsymPoly sig = \case []   -> Just "empty polynomial - this should not happen"
                           x:xs -> if any ((/= arity x) . arity) xs
                                     then Just "polynomial does not have uniform arity"
                                     else listToMaybe $ mapMaybe (verifyArity sig . fromMono) (x:xs)

verifyShufflePoly :: OperadTree a => Signature -> Poly a -> Maybe String
verifyShufflePoly sig ts = case listToMaybe $ mapMaybe (verifyShuffle . fromMono) ts of Nothing -> verifyAsymPoly sig ts; Just s -> Just s

verifyS_ :: OperadTree a => Signature -> [Poly a] -> Maybe String
verifyS_ sig ts = listToMaybe $ mapMaybe (verifyShufflePoly sig) ts

verifyA_ :: OperadTree a => Signature -> [Poly a] -> Maybe String
verifyA_ sig ts = listToMaybe $ mapMaybe (verifyAsymPoly sig) ts