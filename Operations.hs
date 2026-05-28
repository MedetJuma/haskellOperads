{-# LANGUAGE LambdaCase, FlexibleInstances #-}

module Operations where

import Control.Monad
import Data.Maybe
import Data.List

import Utils
import OperadTree


-- Operations class
--   composition and division for shuffle / asymmetric trees

class OperadTree a => Operations a where
  graft         :: [(Int,a)] -> a -> a
  divide1       :: [(Int,a)] -> Maybe [(Int,a)]

instance Operations OT where
  graft = graftShuffle
  divide1 = divideShuffle

instance Operations OTS where
  graft = graftShuffle
  divide1 = divideShuffle

instance Operations AT where
  graft = graftAsym
  divide1 = Just

instance Operations ATS where
  graft = graftAsym
  divide1 = Just



-- Signed class
--   the signed extension for Operations

class Operations a => Signed a where
  divisionSign  :: a -> a -> Bool

instance Signed OTS where
  divisionSign t d = case divide0 t d of Just ts -> divisionSign0 t d + divisionSign1 ts; _ -> error "divisionSign"

instance Signed ATS where
  divisionSign = divisionSign0



-- COMPOSITION

-- Graft a number of trees to given leaves in a tree

graftShuffle :: OperadTree a => [(Int,a)] -> a -> a            
graftShuffle xs t = case splitVertex t of
  Left i       -> lookupWithDefault (\_ -> t) xs i
  Right (ts,f) -> f $ map (graftShuffle xs) ts

graftAsym :: OperadTree a => [(Int,a)] -> a -> a
graftAsym xs t = case splitVertex t of
  Left _       -> case xs of [(_,s)] -> s; _ -> error "graft: wrong number of trees" 
  Right (ts,f) -> f $ g xs ts
    where g xs = \case [] -> []; (t:ts) -> let (us,vs) = splitAt (arity t) xs in graftAsym us t : g vs ts



-- SPLITTING

splits :: OperadTree a => a -> [(a,a -> a)]         
splits t = [(t,id)] ++ case splitVertex t of 
    Left _       -> []
    Right (ts,f) -> [(s, f . (xs++) . (: zs) . g) | (xs,y,zs) <- foci ts, (s,g) <- splits y ]

-- Split with depth cut-off

splitsUpto :: OperadTree a => Int -> a -> [(a,a -> a)]
splitsUpto i t = if depth t < i then [] else [(t,id)] ++ case splitVertex t of
    Left _       -> []
    Right (ts,f) -> [(s, f . (xs++) . (: zs) . g) | (xs,y,zs) <- foci ts, (s,g) <- splitsUpto i y ]

-- Split at a given position

splitat :: OperadTree a => [Int] -> a -> (a,a -> a)
splitat = f where
    f []     t = (t,id)
    f (i:is) t = let Right (ts,h) = splitVertex t; (rs,s:us) = splitAt i ts; (u,g) = f is s
                 in (u, h . (rs++) . (:us) . g)


-- DIVISION

-- divide at the root
-- returns a raw mapping from leaves (of the divisor) to branches (of the divided)

divide0 :: OperadTree a => a -> a -> Maybe [(Int, a)]
divide0 t d | Left i       <- splitVertex d = Just [(i,t)]
            | Right (ds,_) <- splitVertex d, depth d <= depth t,
              Right (ts,_) <- splitVertex t, vertexType d == vertexType t = liftM concat $ sequence $ zipWith divide0 ts ds
            | otherwise = Nothing

-- verifies the raw mapping is monotone (branches preserve the order of leaves)

divideShuffle :: OperadTree a => [(Int,a)] -> Maybe [(Int,a)]
divideShuffle xs | not (null xs), ys <- map snd $ sort xs, isSorted ys = Just (zip [1..] ys)
                 | otherwise = Nothing

-- computes the asymmetric part of the sign of a division

divisionSign0 :: Signed a => a -> a -> Sign
divisionSign0 t d | Right (ds,_) <- splitVertex d,
                    Right (ts,_) <- splitVertex t = f (zip ts ds) + sum (zipWith divisionSign0 ts ds)
                  | otherwise = 0
  where
    f = \case [] -> 0; (t0,d0):tss -> f tss + if depth d0 == 0 then (sign_t t0 * (sum $ map (sign_t . snd) tss)) else 0

-- computes the shuffle part of the sign of a division

divisionSign1 :: Signed a => [(Int,a)] -> Sign
divisionSign1 = permutationSign . map fst . filter (not . sign_t . snd)










