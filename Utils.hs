{-# LANGUAGE LambdaCase #-}

module Utils where


-- A class for every object with a notion of arity

class Arity a where
  arity :: a -> Int


-- A type for positions in trees

type Pos = [Int]


-- Sorted list checks

isSorted :: Ord a => [a] -> Bool
isSorted = \case [] -> True
                 xs -> and . zipWith (<=) xs $ tail xs

isSortedBy :: (a -> a -> Ordering) -> [a] -> Bool
isSortedBy f = \case [] -> True
                     xs -> all (`elem` [LT,EQ]) . zipWith f xs $ tail xs

isSortedStrictly :: Ord a => [a] -> Bool
isSortedStrictly = \case [] -> True
                         xs -> and . zipWith (<) xs $ tail xs
isSortedStrictlyBy :: (a -> a -> Ordering) -> [a] -> Bool
isSortedStrictlyBy _ [] = True
isSortedStrictlyBy f xs = all (==LT) $ zipWith f xs $ tail xs


-- Count consecutive elements

countElems :: Eq a => [a] -> [Int]
countElems = \case []   -> []
                   x:xs -> let (ys,zs) = break (x/=) xs in (1 + length ys) : countElems zs    


-- Lookup with default action

lookupWithDefault :: Eq a => (a -> b) -> [(a,b)] -> a -> b
lookupWithDefault f xys x = case lookup x xys of Just y -> y; Nothing -> f x


-- Generate all one-hole contexts of a list

foci :: [a] -> [([a],a,[a])]
foci [] = []
foci (x:xs) = ([],x,xs) : [ (x:ys,y,zs) | (ys,y,zs) <- foci xs ]




strictSplitWhile :: Ord a => a -> [a] -> ([a],[a])
strictSplitWhile a xs = g xs id
  where
    g xs0 cc | (x:xs) <- xs0, x < a = g xs (cc.(x:))
             | otherwise = (cc [], dropWhile (== a) xs0)

