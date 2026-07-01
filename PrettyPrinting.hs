{-# LANGUAGE LambdaCase, FlexibleInstances, TypeSynonymInstances, UndecidableInstances #-}

module PrettyPrinting where

import Data.List
import Data.Ratio

import Utils()
import Signature
import OperadTree
import Polynomials
import Measure (showMeasure)
import CriticalPairs


-- PRETTY PRINTING

class PPrint a where
  pp  :: Signature -> a -> String
  ppr :: Signature -> a -> IO ()
  ppa :: Signature -> a -> IO (a)

  ppr sig = putStrLn . pp sig
  ppa sig x = ppr sig x >> return x


instance PPrint a => PPrint [Maybe a] where
  pp sig xs = intercalate "\n" (map f xs) 
    where f Nothing = " --- "
          f (Just a) = pp sig a

instance (OperadTree a, PPrint a) => PPrint (a -> a) where
  pp sig f = "Context: " ++ pp sig (f $ leaf 0) ++ "  Branches: " ++ intercalate " " (map (pp sig . f . leaf) [1..10])


ppScalar :: Scalar -> (Bool,String)
ppScalar i = let j = abs i; n = numerator j; m = denominator i;
             in (signum i /= -1, 
                  if j == 1 then  ""
                            else (show n ++ if m == 1 then " " else ("/" ++ show m ++ " ")) )

ppMono_ :: PPrint a => Signature -> Mono a -> String
ppMono_ sig (t,_,i) = let (b,str) = ppScalar i in "  " ++ (if b then "+" else "-") ++ "  " ++ str ++ pp sig t

ppSignatureM :: PPrint a => Signature -> Mono a -> String
ppSignatureM sig (t,_,_) =
  pp sig t

instance PPrint a => PPrint (Poly a) where
  pp sig = \case []         -> "*"
                 (t,_,i):ms -> let (b,str) = ppScalar i in (if b then "" else "- ") ++ str ++ pp sig t ++ concatMap (ppMono_ sig) ms

instance PPrint a => PPrint [Poly a] where
  pp sig ps = intercalate "\n" (map (pp sig) ps)

instance PPrint a => PPrint (Rewrite a) where
  pp sig (Rewrite r _ ps) =
    pp sig r ++ "  ->  " ++ pp sig ps

ppRewrite :: PPrint a => Bool -> Signature -> Rewrite a -> String
ppRewrite leading sig (Rewrite r _ ps) =
  if leading
    then pp sig r
    else pp sig r ++ "  ->  " ++ pp sig ps

ppRewrites :: PPrint a => Bool -> Signature -> [Rewrite a] -> String
ppRewrites leading sig = intercalate "\n\n  " . map (ppRewrite leading sig)

instance PPrint a => PPrint [Rewrite a] where
  pp sig xs = intercalate "\n\n  " (map (pp sig) xs)

instance PPrint a => PPrint (CriticalPair a) where
  pp sig (CP _ t pos r1 r2) =
    let t' = pp sig t
        p' = "pos: " ++ intercalate "." (map show pos)
        l  = length t' - length p'
        s  = replicate (abs l) ' '
    in t' ++ (if l < 0 then s else "") ++ "     " ++ pp sig r1 ++ "\n" ++
       p' ++ (if l > 0 then s else "") ++ "     " ++ pp sig r2

instance PPrint a => PPrint [CriticalPair a] where
  pp sig xs = intercalate "\n" $ map (pp sig) xs



ppTree :: (PPrint a, OperadTree a) => Signature -> a -> String
ppTree sig t = case splitVertex t of
  Left i       -> if i == 0 then "*" else show i
  Right (ts,_) -> case vertexType t of
    Just i  -> if i >= 0 && i < length sig
               then let op = sig !! i
                    in name op ++ [open (bracket op)]
                               ++ intercalate " " (map (pp sig) ts)
                               ++ [close (bracket op)]
               else "(-1)" ++ [open "()"] ++ intercalate " " (map (pp sig) ts) ++ [close "()"]
    Nothing -> error "ppTree: missing vertex type"

instance PPrint OT where
  pp = ppTree

instance PPrint OTS where
  pp = ppTree

instance PPrint AT where
  pp = ppTree

instance PPrint ATS where
  pp = ppTree
