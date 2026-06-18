{-# LANGUAGE LambdaCase #-}

module Generation where

import Control.Arrow
import Control.Monad
import Data.Maybe
import Control.DeepSeq
import Control.Parallel.Strategies

import Utils
import Signature
import OperadTree
import Operations



normalTrees :: (Operations a, NFData a) => Signature -> [a] -> Int -> [a]
normalTrees sig ds = last . normalTreesUpto sig ds

normalShuffleTrees :: (Operations a, NFData a) => Signature -> [a] -> Int -> [a]
normalShuffleTrees sig ds = last . normalShuffleTreesUpto sig ds
 
 -- count trees which do not contain leading terms of Groebner basis as its fragments.
normalTreesUpto :: (Operations a, NFData a) => Signature -> [a] -> Int -> [[a]]
normalTreesUpto sig ds i
 | i <= 0 = [[]]
 | i == 1 = [[],[leaf 0]]
 | otherwise =
     let ts = normalTreesUpto sig ds (i-1)
         f (k,op) = sumsOfLength (arity op) i 1 >>= (map (vertexS k $ sgn op) . sequence . map (ts !!)) `using` parListChunk 16 rdeepseq
         candidates = concatMap f (zip [0..] sig)
         keepMaskNS = map (isNormal0 ds) candidates `using` parListChunk 16 rdeepseq
         ns         = [ c | (c, True) <- zip candidates keepMaskNS ]
     in ts ++ [ns]

normalShuffleTreesUpto :: (Operations a, NFData a) => Signature -> [a] -> Int -> [[a]]
normalShuffleTreesUpto sig ds i
 | i <= 0 = [[]]
 | i == 1 = [[],[leaf 1]]
 | otherwise =
     let ts = normalShuffleTreesUpto sig ds (i-1)
         f (k,op) = sumsOfLength (arity op) i 1 >>= (concatMap (shuffleVertex k (sgn op)) . sequence . map (ts !!)) `using` parListChunk 16 rdeepseq
         ns = filter (isNormal0S ds) . concatMap f $ zip [0..] sig
     in ts ++ [ns]

shuffleVertex :: (Operations a, NFData a) => Int -> Bool -> [a] -> [a]
shuffleVertex i b ts = let l = length ts
                           f 0    []  t = [t]
                           f i (x:xs) t = allGrafts x t i >>= f (i-1) xs
                       in f l ts . vertexS i b $ map leaf [1..l]

allGrafts :: (Operations a, NFData a) => a -> a -> Int -> [a] 
allGrafts s t i = let m = arity s
                      n = arity t
                      r = relabel (+n) s
                  in [ relabel f $ graft [(i,r)] t | f <- merge [1..n] [n+1..n+m] [(i,n+1)] ]

isNormal0 :: (OperadTree a, NFData a) => [a] -> a -> Bool
isNormal0 rs t = all (isNothing . divide0 t) rs

isNormal0S :: (OperadTree a, NFData a) => [a] -> a -> Bool
isNormal0S rs t = all (isNothing . (divide0 t >=> divideShuffle)) rs

----------

-- Generates all binary trees
--   allBinaryTrees
--     <sign. size>   Number of vertex types
--     <leaves>       Number of leaves

allBinaryTrees :: Int -> Int -> [OT]
allBinaryTrees m n = let sig = [ (v,2) | v <- [0..m-1] ] in concatMap (allLeafOrders n) (allNonUnaryFrames sig n)


-- Generates all non-unary trees
--   allNonUnaryTrees
--     <signature>    List of pairs <vertexID> <arity>
--     <leaves>       Number of leaves 

allNonUnaryTrees :: [(Int, Int)] -> Int -> [OT]
allNonUnaryTrees sig n = concatMap (allLeafOrders n) (allNonUnaryFrames sig n)

-- Generates all trees
--   allUnreducedTrees
--     <signature>    List of pairs <vertexID> <arity>
--     <leaves>       Number of leaves
--     <corollas>     Number of corollas

allUnreducedTrees :: [(Int, Int)] -> Int -> Int -> [OT]
allUnreducedTrees sig n c = concatMap (allLeafOrders n) (allUnreducedFrames sig n c)


-- Generates all leaf orderings for a given tree-frame

allLeafOrders :: Int -> OT -> [OT]
allLeafOrders n t = f [1..n] t
  where
    f [x] (L 0)     = [ L x ]
    f xs (V v d ts) = [ V v d rs | rs <- g xs ts ]
    g xs []         = [ [] ]
    g xs (t:ts)     = [ r:rs | (ys,zs) <- unshuffle (arity t-1) (tail xs), r <- f (head xs : ys) t, rs <- g zs ts ]


-- Generates all trees with specification:
--   allNonUnaryFrames 
--       <signature>   list of pairs of <vertexname> with <arity>
--       <leaves>      number of leaves in the tree

allNonUnaryFrames :: [(Int,Int)] -> Int -> [OT]
allNonUnaryFrames sig = if minimum (map snd sig) < 2 then error "signature contains operator of arity < 2" else f where
  f n | n == 1 = [L 0]
      | n <  1 = []
      | otherwise =  concat [ map (vertex v) (mapM f ns) | (v,a) <- sig, ns <- sumsOfLength a n 1 ]



-- Generates all trees with specification:
--   allUnreducedFrames 
--       <signature>   list of pairs of <vertexname> with <arity>
--       <leaves>      number of leaves in the tree
--       <corollas>    number of corollas in the tree

allUnreducedFrames :: [(Int,Int)] -> Int -> Int -> [OT]
allUnreducedFrames sig =  if minimum (map snd sig) < 1 then error "signature contains operator of arity < 1" else f where
  mm = minimum $ map snd sig
  mx = maximum $ map snd sig
  f n c | c == 0 = if n == 1 then [L 0] else []
        | n <= c * (mm-1) = []
        | n >  c * (mx-1) + 1 = []
        | otherwise =  concat [ map (V v 0) $  g ns cs | (v,a) <- sig, ns <- sumsOfLength a n 1, cs <- sumsOfLength a (c-1) 0]
  g [] [] = [[]]
  g (n:ns) (c:cs) = [ t:ts | t <- f n c, ts <- g ns cs]



-- Un-shuffling

unshuffle :: Int -> [a] -> [([a],[a])]
unshuffle i xs = f i (length xs-i) xs
  where
    f i j xs | i <= 0 = [([],xs)]
             | j <= 0 = [(xs,[])]
             | (x:xs') <- xs = map ((x:) *** id) (f (i-1) j xs') ++ 
                               map (id *** (x:)) (f i (j-1) xs')


-- All Shuffles
-- of two lists into one

allShuffles :: [a] -> [a] -> [[a]] 
allShuffles = f where
  f xs [] = [xs]
  f [] ys = [ys]
  f xs ys = map (head xs :) (f (tail xs) ys) ++
            map (head ys :) (f xs (tail ys)) 


-- Merging
-- of two linear orders with overlapping points
--   merge <list1> <list2> <merge points>
-- assumes both lists and both projections to be sorted

merge :: [Int] -> [Int] -> [(Int,Int)] -> [Int -> Int]
merge xs ys = map (lookupWithDefault id) . merge_ xs ys

merge_ :: [Int] -> [Int] -> [(Int,Int)] -> [[(Int,Int)]]
merge_ xs ys = map (filter (uncurry (/=))) . f 1 xs ys
  where
    f i xs ys = \case
      []          -> map (flip zip [i..]) $ allShuffles xs ys
      ((x,y):xys) -> let (xs1,xs2) = strictSplitWhile x xs
                         (ys1,ys2) = strictSplitWhile y ys
                         xys1      = map (flip zip [i..]) $ allShuffles xs1 ys1
                         n         = i + length xs1 + length ys1
                     in [ a ++ (x,n) : (y,n) : b | a <- xys1, b <- f (n+1) xs2 ys2 xys ]


-- Generates all integer lists with specification
--   sumsOfLength 
--      <length>   exact length
--      <sum>      sum of elements
--      <min>      minimum of list

sumsOfLength :: Int -> Int -> Int -> [[Int]]
sumsOfLength l n min = let m = n - (l*min) in
  if l == 0 && n == 0  then [[]] else
  if l <  0 || m <  0  then []   else
     [ i:is | i <- [m+min,m+min-1..min], is <- sumsOfLength (l-1) (n-i) min]
