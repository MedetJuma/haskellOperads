{-# LANGUAGE LambdaCase, DeriveGeneric, DeriveAnyClass #-}

module Measure where

import Control.Arrow
import Data.List
import Data.Ord
import Control.DeepSeq (NFData)
import GHC.Generics (Generic)

import Utils
import Signature
import OperadTree

-- Data for constructing a measure

data MeasureData = MD {arityMD :: Int, vertices :: [Int], leafOrder :: [Int], paths :: [[Int]]}

instance Arity MeasureData where
  arity = arityMD

-- Measures on operad trees

data Measure = End
             | Ar        Int          Measure
             | Deg      [Int]         Measure
             | Perm     [Int]         Measure
             | PermR    [Int]         Measure
             | DegLex   [(Int,[Int])] Measure
             | DegLexR  [(Int,[Int])] Measure
             | Weighted [Int]         Measure
             deriving (Eq,Ord,Show,Generic, NFData)

showMeasure :: Measure -> String
showMeasure = \case
  End   -> ""
  Ar _ m -> "arity " ++ showMeasure m
  Deg _ m -> "degree " ++ showMeasure m
  Perm _ m -> "permutation " ++ showMeasure m
  PermR _ m -> "reverse permutation " ++ showMeasure m
  DegLex _ m -> "degree-lexicographic " ++ showMeasure m
  DegLexR _ m -> "reverse degree-lexicographic " ++ showMeasure m
  Weighted _ m -> "weighted " ++ showMeasure m


measure_ :: OperadTree a => a -> MeasureData
measure_ t = uncurry (MD (arity t) $ vertexTypes t) $ leavesPaths t

measure :: OperadTree a => Weighting -> a -> Measure -> Measure
measure w t = let d = measure_ t
                  f = \case
                        End   -> End
                        Ar _ m -> Ar (arity d) $ f m
                        Deg _ m -> Deg (map length $ paths d) $ f m
                        Perm _ m -> Perm (leafOrder d) $ f m
                        PermR _ m -> PermR (map negate $ leafOrder d) $ f m
                        DegLex _ m -> DegLex (map (length &&& id) $ paths d) $ f m
                        DegLexR _ m -> DegLexR (map (negate . length &&& id) $ paths d) $ f m
                        Weighted _ m -> Weighted (sortBy (flip compare) . map w $ vertices d) $ f m
              in f


