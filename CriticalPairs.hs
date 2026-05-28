{-# LANGUAGE LambdaCase #-}

module CriticalPairs where

import Control.Arrow
import Control.Monad
import Data.Maybe
import Data.List

import Utils
import OperadTree
import Measure
import Polynomials
import Generation
import Operations



-- Rewrite rules


type Rewrite a = (a, Measure, Poly a)


rwToPoly :: OperadTree a => Field -> Rewrite a -> Poly a
rwToPoly z (t,r,ps) = [(t,r,1)] ++ map (\(x,y,i) -> (x,y,neg_ z i)) ps 

polyToRw :: OperadTree a => Field -> Poly a -> Maybe (Rewrite a)
polyToRw z p = case canonical z p of [] -> Nothing; ((t,m,_):q) -> Just (t,m, map (\(x,y,i) -> (x,y,neg_ z i)) q)



-- Smallest Common Multiples

class OperadTree a => CriticalPairs a where
  scm :: Bool -> a -> a -> [(a,Pos)]

instance CriticalPairs OT where
  scm = scm2_

instance CriticalPairs OTS where
  scm = scm2_

instance CriticalPairs AT where
  scm = scm1A

instance CriticalPairs ATS where
  scm = scm1A


-- scm0
-- attempt to merge two trees at the root to find a common multiple
--   assumes trees with disjoint leaf sets
--   returns a triple of: 
--     - the tree
--     - the position where t divides s, i.e. the root
--     - the (valid, sorted) minimal leaf values at the boundary

scm0_ :: OperadTree a => a -> a -> Maybe (a,Pos,[(Int,Int)]) -- SMALLEST COMMON MULTIPLE
scm0_ s t | Just (r,xs) <- f s t, ys <- sort xs, isSorted (map snd ys) = Just (r,[],ys)
          | otherwise = Nothing
  where
    f s t | Left i <- splitVertex s = Just (t,[(i,minleaf t)])
          | Left i <- splitVertex t = Just (s,[(minleaf s,i)])
          | Right (rs,g) <- splitVertex s, vertexType s == vertexType t,
            Right (ts,_) <- splitVertex t, Just xs <- zipWithM f rs ts   = Just (g $ map fst xs, concatMap snd xs)
          | otherwise = Nothing


-- A simplified version for the asymmetric case

scm0A :: OperadTree a => a -> a -> Maybe a
scm0A s t | Left i <- splitVertex s = Just t
          | Left i <- splitVertex t = Just s
          | Right (rs,g) <- splitVertex s, vertexType s == vertexType t,
            Right (ts,_) <- splitVertex t, Just xs <- zipWithM scm0A rs ts = Just (g xs)
          | otherwise = Nothing


-- scm1 <bool> <tree1> <tree2>  =  [ (<cm>,<pos>,<bound>) ]
--   finds common multiples <cm> which:
--        <tree1> divides at the root
--        <tree2> divides at <pos>
--        with boundary <bound>
--   boolean flag indicates whether to include root case
--   assumes disjoint leaf sets

scm1_ :: OperadTree a => Bool -> a -> a -> [(a,Pos,[(Int,Int)])]
scm1_ b s t = case splitVertex s of
  Left _       -> []
  Right (ts,g) -> (if b then maybeToList (scm0_ s t) else []) ++ (concatMap f $ zip [0..] $ foci ts)
    where
      f (i,(ts0,u,ts1)) = map (\(r,is,xs) -> (g (ts0 ++ [r] ++ ts1),i:is,xs)) (scm1_ True u t)


-- Simplified for asymmetric case

scm1A :: OperadTree a => Bool -> a -> a -> [(a,[Int])]
scm1A b s t = map (reset *** id) $ case splitVertex s of
  Left _       -> []
  Right (ts,g) -> root ++ (concatMap f $ zip [0..] $ foci ts)
    where
      root | b, Just r <- scm0A s t = [(r,[])]
           | otherwise = []
      f (i,(ts0,u,ts1)) = map (g . (ts0++) . (:ts1) *** (i:)) (scm1A True u t)


-- scm2
-- find non-trivial critical pairs of two trees (in one direction)

scm2_ :: OperadTree a => Bool -> a -> a -> [(a,[Int])]
scm2_ b s t = let m = arity s
                  n = arity t
                  u = relabel (+m) t 
              in [ (relabel f r,is) | (r,is,xs) <- scm1_ b s u, f <- merge [1..m] [m+1..m+n] xs]
              -- relabel is adding all possible labelings on a skeleton






-- Critical Pairs

data CriticalPair a = CP {arityCP   :: Int,
                          cm        :: a,
                          other     :: Pos,
                          rwRoot    :: Rewrite a, 
                          rwOther   :: Rewrite a }

instance Arity (CriticalPair a) where
  arity = arityCP


-- Find critical pairs of two rewrites
--   Boolean flag indicates two identical rewrites
--   (these are compared only in one direction, and not at the root)

criticalPairs :: CriticalPairs a => Bool -> Rewrite a -> Rewrite a -> [CriticalPair a]
criticalPairs b r1@(t1,_,_) r2@(t2,_,_) = (if b then [] else
   [ CP (arity s) s p r1 r2 | (s,p) <- scm True  t1 t2]) ++ 
   [ CP (arity s) s p r2 r1 | (s,p) <- scm False t2 t1]


-- Find critical pairs of <theory1> with <theory2> 

relativeCPs :: CriticalPairs a => [Rewrite a] -> [Rewrite a] -> [CriticalPair a]
relativeCPs xs ys = concat [ criticalPairs False x y | x <- xs, y <- ys ]

relativeCPsCount :: CriticalPairs a => [Rewrite a] -> [Rewrite a] -> ([CriticalPair a], Int)
relativeCPsCount xs ys = (concat results, length xs * length ys)
  where results = [ criticalPairs False x y | x <- xs, y <- ys ]

-- Find critical pairs internal to a theory

selfCPs :: CriticalPairs a => [Rewrite a] -> [CriticalPair a]
selfCPs = \case [] -> []
                x:xs -> criticalPairs True x x ++ concatMap (criticalPairs False x) xs ++ selfCPs xs


-- Test whether a rewrite rule divides a tree (helper for redundancy checks)
divides :: Operations a => Rewrite a -> a -> Bool
divides (d,_,_) t = any (\(s,_) -> isJust (divide0 s d >>= divide1)) (splits t)


-- Buchberger's triangle lemma: a critical pair is redundant if there
-- exists a rewrite rule c in the given list such that c's left-hand side
-- is not the same as the root or other rule's left-hand side, and c
-- divides the common multiple `cm` of cp.
isRedundant :: (Operations a, Eq a) => [Rewrite a] -> CriticalPair a -> Bool
isRedundant rws cp = any check rws
  where
    (rootL,_,_)  = rwRoot cp
    (otherL,_,_) = rwOther cp
    rootReset  = reset rootL
    otherReset = reset otherL
    check rw@(t,_,_) = let tR = reset t
                       in tR /= rootReset && tR /= otherReset && divides rw (cm cp)


