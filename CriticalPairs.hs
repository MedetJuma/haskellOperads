{-# LANGUAGE LambdaCase, DeriveAnyClass, DeriveGeneric, DuplicateRecordFields #-}

module CriticalPairs where

import Control.Arrow
import Control.DeepSeq
import Control.Monad
import Data.Maybe
import Data.List
import GHC.Generics (Generic)

import Utils
import OperadTree
import Measure
import Polynomials
import Generation
import Operations



-- Rewrite rules

data Rewrite a = Rewrite
  { rwTree      :: a
  , rwMeasure   :: Measure
  , rwPoly      :: Poly a
  , signatureM  :: Mono a
  , signatureL  :: Int
  } deriving (Eq, Show, Generic, NFData)


rwToPoly :: OperadTree a => Field -> Rewrite a -> Poly a
rwToPoly z (Rewrite t r ps _ _) = [(t,r,1)] ++ map (\(x,y,i) -> (x,y,neg_ z i)) ps 

polyToRw :: OperadTree a => Field -> Poly a -> Maybe (Rewrite a)
polyToRw z p = case canonical z p of [] -> Nothing; ((t,m,_):q) -> Just (Rewrite t m (map (\(x,y,i) -> (x,y,neg_ z i)) q) (t,m,1) 0)



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
    f s0 t0 | Left i <- splitVertex s0 = Just (t0,[(i,minleaf t0)])
            | Left i <- splitVertex t0 = Just (s0,[(minleaf s0,i)])
            | Right (rs,g) <- splitVertex s0, vertexType s0 == vertexType t0,
              Right (ts,_) <- splitVertex t0, Just xs <- zipWithM f rs ts   = Just (g $ map fst xs, concatMap snd xs)
          | otherwise = Nothing


-- A simplified version for the asymmetric case

scm0A :: OperadTree a => a -> a -> Maybe a
scm0A s t | Left _ <- splitVertex s = Just t
          | Left _ <- splitVertex t = Just s
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

data CriticalPair a = CP {arityCP    :: Int,
                          cm         :: a, -- the common multiple
                          other      :: Pos, -- the vertex in the common multiple where the second rule is applied
                          rwRoot     :: Rewrite a, -- the first rewrite rule
                          rwOther    :: Rewrite a, -- the second rewrite rule
                          signatureM :: Mono a, -- the monomial of the critical pair
                          signatureL :: Int        -- the signature index of the critical pair
}

instance Arity (CriticalPair a) where
  arity = arityCP


-- Find critical pairs of two rewrites
--   Boolean flag indicates two identical rewrites
--   (these are compared only in one direction, and not at the root)

criticalPairs :: (CriticalPairs a, Operations a) => Bool -> Rewrite a -> Rewrite a -> [CriticalPair a]
criticalPairs b r1@(Rewrite t1 _ _ _ _) r2@(Rewrite t2 _ _ _ _) = (if b then [] else
   [ mkCP r1 r2 s p | (s,p) <- scm True  t1 t2]) ++ 
   [ mkCP r2 r1 s p | (s,p) <- scm False t2 t1]
  where
    mkCP root otherRule s p = CP
      { arityCP    = arity s
      , cm         = s
      , other      = p
      , rwRoot     = root
      , rwOther    = otherRule
      , signatureM = fst (criticalPairSignature root otherRule s p)
      , signatureL = snd (criticalPairSignature root otherRule s p)
      }
      

    -- Pattern match here to extract rootSigL and otherSigL unambiguously
    criticalPairSignature root@(Rewrite _ _ _ _ rootSigL) otherRule@(Rewrite _ _ _ _ otherSigL) cmTree p =
      let sigRoot  = (liftSignature root cmTree, rootSigL)
          sigOther = (liftSignatureOther otherRule cmTree p, otherSigL)
      in if comparePOT sigRoot sigOther == GT
            then sigRoot
            else sigOther

    comparePOT (m1, l1) (m2, l2) = 
      case compare l1 l2 of
        EQ  -> compare m1 m2
        res -> res

    -- Pattern match to extract 'tree' and 'sigM'
    liftSignature (Rewrite tree _ _ sigM _) cmTree =
      case divide0 cmTree tree >>= divide1 of
        Just ts -> let (sigTree, sigMeasure, sigScalar) = sigM
                   in (graft ts sigTree, sigMeasure, sigScalar)
        Nothing -> error "liftSignature: division failed"

    -- Pattern match to extract 'tree' and 'sigM'

    liftSignatureOther (Rewrite tree _ _ sigM _) cmTree pos =
      let (s_pos, g) = splitat pos cmTree  -- 1. Capture the context 'g'
      in case divide0 s_pos tree >>= divide1 of
          Just ts -> let (sigTree, sigMeasure, sigScalar) = sigM
                      in (g (graft ts sigTree), sigMeasure, sigScalar) -- 2. Apply 'g'
          Nothing -> error "liftSignatureOther: division failed"

-- Find critical pairs of <theory1> with <theory2> 

relativeCPs :: (CriticalPairs a, Operations a) => [Rewrite a] -> [Rewrite a] -> [CriticalPair a]
relativeCPs xs ys = concat [ criticalPairs False x y | x <- xs, y <- ys ]

relativeCPsCount :: (CriticalPairs a, Operations a) => [Rewrite a] -> [Rewrite a] -> ([CriticalPair a], Int)
relativeCPsCount xs ys = (concat results, length xs * length ys)
  where results = [ criticalPairs False x y | x <- xs, y <- ys ]

-- Find critical pairs internal to a theory

selfCPs :: (CriticalPairs a, Operations a) => [Rewrite a] -> [CriticalPair a]
selfCPs = \case [] -> []
                x:xs -> criticalPairs True x x ++ concatMap (criticalPairs False x) xs ++ selfCPs xs


-- Test whether a rewrite rule divides a tree (helper for redundancy checks)
-- divides :: Operations a => Rewrite a -> a -> Bool
-- divides (d,_,_) t = any (\(s,_) -> isJust (divide0 s d >>= divide1)) (splits t)

-- Buchberger's triangle lemma: a critical pair is redundant if there
-- exists a rewrite rule c in the given list such that c's left-hand side
-- is not the same as the root or other rule's left-hand side, and c
-- divides the common multiple `cm` of cp.

-- !!ONLY THE FIRST CONDITION IS CHECKED. Durys emes degen soz, janadan jazaiyk
-- isRedundant :: (Operations a, Eq a) => [Rewrite a] -> CriticalPair a -> Bool
-- isRedundant rws cp = any check rws
--   where
--     (rootL,_,_)  = rwRoot cp
--     (otherL,_,_) = rwOther cp
--     rootReset  = reset rootL
--     otherReset = reset otherL
--     check rw@(t,_,_) = let tR = reset t
--                        in tR /= rootReset && tR /= otherReset && divides rw (cm cp)

-- Check if one tree structurally divides another
treeDivides :: Operations a => a -> a -> Bool
treeDivides d t = any (\(s,_) -> isJust (divide0 s d >>= divide1)) (splits t)

-- Proper division
properDivides :: (Operations a, OperadTree a, Eq a) => a -> a -> Bool
properDivides d t = treeDivides d t && reset d /= reset t

-- Buchberger's triangle lemma for operads
isRedundant :: (Operations a, CriticalPairs a, Eq a) => [Rewrite a] -> CriticalPair a -> Bool
isRedundant rws cp = any check rws
  where
    Rewrite rootL _ _ _ _  = rwRoot cp
    Rewrite otherL _ _ _ _ = rwOther cp
    cmT          = cm cp
    
    rootReset  = reset rootL
    otherReset = reset otherL
    
    -- Generates all possible common multiples between trees t1 and t2
    allCommonMultiples t1 t2 = map fst (scm True t1 t2) ++ map fst (scm False t2 t1)
    
    check (Rewrite t3 _ _ _ _) = 
      let t3Reset = reset t3
      in t3Reset /= rootReset && 
         t3Reset /= otherReset && 
         -- Condition 1 from Corollary 3.5.3.3 / 5.5.3.3 (Bremner, Dotsenko):
         treeDivides t3 cmT && 
         
         -- Condition 2 from Corollary 3.5.3.3 / 5.5.3.3 (Bremner, Dotsenko):
         
         -- Exists a common multiple T' of (rootL, t3) that properly divides cmT
         any (`properDivides` cmT) (allCommonMultiples rootL t3) &&
         
         -- Exists a common multiple T'' of (t3, otherL) that properly divides cmT
         any (`properDivides` cmT) (allCommonMultiples t3 otherL)

-- Faugere's F5 criterion for operads
isRedundantF5 :: (Operations a, CriticalPairs a, Eq a) => [Rewrite a] -> CriticalPair a -> Bool
isRedundantF5 rws cp = any check rws
  where
    CP _ _ _ (Rewrite rootL _ _ _ _) (Rewrite otherL _ _ _ _) sigM sigL = cp
    cmT = cm cp
    sigTree = fromMono sigM
    
    rootReset  = reset rootL
    otherReset = reset otherL
    
    allCommonMultiples t1 t2 = map fst (scm True t1 t2) ++ map fst (scm False t2 t1)

    check (Rewrite t3 _ _ _ ind3) = 
      let t3Reset = reset t3
      in t3Reset /= rootReset && 
         t3Reset /= otherReset && 
         
         -- 1. F5 index comparison
         (ind3 < sigL) && 
         
         -- 2. F5 Divison 
         properDivides t3 sigTree -- &&
         
        -- 3. Dotsenko-Khoroshkin type condition???
        --  any (`properDivides` cmT) (allCommonMultiples rootL t3) &&
        --  any (`properDivides` cmT) (allCommonMultiples t3 otherL)

-- Execute as follows
-- cabal run OperadsHaskell1 -- +RTS -N4 -qa -A64m
-- -A64m garbage collector 64 Mb
-- -qa pins specific threads. One can also use taskset 0, 1, 2, 3, ...
-- -N4 runs on the program 4 cores
