module Rewriting where

import Control.Arrow
import Control.Monad
import Data.Maybe
import Data.List
import Control.DeepSeq
import Control.Parallel.Strategies

import Utils
import Signature
import OperadTree
import Operations
import Polynomials
import Measure
import CriticalPairs


--------------

-- Rewriting class
--   Signed / unsigned rewriting
--   The basic function takes the following arguments
--
--   rewrite0 <rule> <tree> <context> <scalar>

class (Operations a, CriticalPairs a) => Rewriting a where
  rewrite0 :: Weighting -> Field -> Rewrite a -> a -> (a -> a) -> Scalar -> Maybe (Poly a)

instance Rewriting OT where
  rewrite0 = rewrite0_

instance Rewriting OTS where
  rewrite0 = rewrite0_S

instance Rewriting AT where
  rewrite0 = rewrite0_

instance Rewriting ATS where
  rewrite0 = rewrite0_S

divide0Count :: OperadTree a => a -> a -> (Maybe [(Int,a)], Int)
divide0Count t d = case splitVertex d of
  Left i -> (Just [(i,t)], 1)
  Right (ds,_) | depth d <= depth t,
                 Right (ts,_) <- splitVertex t,
                 vertexType d == vertexType t ->
      let results = zipWith divide0Count ts ds
          (rs, cs) = unzip results
      in if any isNothing rs
            then (Nothing, 1 + sum cs)
            else (Just $ concatMap fromJust rs, 1 + sum cs)
  _ -> (Nothing, 1)

rewrite0_ :: (Operations a, OperadTree a) => Weighting -> Field -> Rewrite a -> a -> (a -> a) -> Scalar -> Maybe (Poly a)
rewrite0_ w z (Rewrite d _ poly) t f i = case divide0 t d >>= divide1 of
                                   Just ts -> let g (u,m,j) = let s = f $ graft ts u in (s, measure w s m, mul_ z i j) in Just $ map g poly
                                   Nothing -> Nothing

rewrite0_S :: (Signed a, OperadTree a) => Weighting -> Field -> Rewrite a -> a -> (a -> a) -> Scalar -> Maybe (Poly a)
rewrite0_S w z (Rewrite d _ poly) t f i = let ts0 = divide0 t d in
  case ts0 >>= divide1 of
      Just ts -> let b         = divisionSign0 t d /= divisionSign1 (fromJust ts0)
                     g (u,m,j) = let v = graft ts u; s = f v in (s, measure w s m, mul_ z i $ mul_ z j $ sign z (b /= divisionSign v u))
                 in Just $ map g poly 
      Nothing -> Nothing

rewrite0Count :: Rewriting a => Weighting -> Field -> Rewrite a -> a -> (a -> a) -> Scalar -> (Maybe (Poly a), Int)
rewrite0Count w z rw@(Rewrite d _ poly) t f i =
  let (_res, c0) = divide0Count t d
      c1 = 1
      cPoly = length poly
      output = rewrite0 w z rw t f i
  in (output, c0 + c1 + cPoly)

copySignature :: Rewrite a -> Rewrite a -> Rewrite a
copySignature (Rewrite t m p) (Rewrite _ _ _) = Rewrite t m p

copySignatureL :: Rewrite a -> Rewrite a -> Rewrite a
copySignatureL (Rewrite t m p) (Rewrite _ _ _) = Rewrite t m p


---------------

-- Rewrite a monomial

rewriteMono :: Rewriting a => Weighting -> Field -> Rewrite a -> Mono a -> Maybe (Poly a)
rewriteMono w z rw@(Rewrite d _ _) (t,_,i) = let f (s,g) = rewrite0 w z rw s g i
                                     in listToMaybe . mapMaybe f $ splitsUpto (depth d) t

-- Rewrite a polynomial

rewritePoly :: Rewriting a => Weighting -> Field -> Rewrite a -> Poly a -> Maybe (Poly a)
rewritePoly w z rw = let f (p,m,q) = liftM ((p++).(++q)) $ rewriteMono w z rw m in listToMaybe . mapMaybe f . foci

rewriteMonoCount :: Rewriting a => Weighting -> Field -> Rewrite a -> Mono a -> (Maybe (Poly a), Int)
rewriteMonoCount w z rw@(Rewrite d _ _) (t,_,i) = -- 28 operations (divisibility etc)
  let go [] cnt = (Nothing, cnt)
      go ((s,g):xs) cnt =
        let (res, c) = rewrite0Count w z rw s g i
        in case res of
             Just p  -> (Just p, cnt + c)
             Nothing -> go xs (cnt + c)
  in go (splitsUpto (depth d) t) 0

rewritePolyCount :: Rewriting a => Weighting -> Field -> Rewrite a -> Poly a -> (Maybe (Poly a), Int)
rewritePolyCount w z rw p = -- 14 operations ()
  let go [] cnt = (Nothing, cnt)
      go ((pre,m,post):ms) cnt =
        let (res, c) = rewriteMonoCount w z rw m
        in case res of
             Just q  -> (Just $ pre ++ q ++ post, cnt + 1 + c)
             Nothing -> go ms (cnt + 1 + c)
  in go (foci p) 0

-- Apply a list of rewrite rules to a polynomial 

rewrites :: Rewriting a => Weighting -> Field -> [Rewrite a] -> Poly a -> Maybe (Poly a)
rewrites w z rws p = listToMaybe $ mapMaybe (\rw -> rewritePoly w z rw p) rws 

rewritesCount :: Rewriting a => Weighting -> Field -> [Rewrite a] -> Poly a -> (Maybe (Poly a), Int)
rewritesCount w z rws p = -- 2 operations (stb size)
  let go [] cnt = (Nothing, cnt)
      go (rw:rws') cnt =
        let (res, c) = rewritePolyCount w z rw p
            cnt' = cnt + c + 1
        in case res of
             Just q  -> (Just q, cnt')
             Nothing -> go rws' cnt'
  in go rws 0

-- Normalise a polynomial by a theory
--   A flag indicates the original was already normal

-- normalise bottom up
normalise :: Rewriting a => Weighting -> Field -> [Rewrite a] -> Poly a -> Poly a
normalise w z rws = f where
   f p = let q = canonical z p -- redoing this will make you run through the polynomial again
    in case rewrites w z rws q of -- rewrites takes roughly 50 operations on average
       Nothing -> q;
        Just r -> f r

normaliseCount :: (Rewriting a, NFData a, NFData (Poly a)) => Weighting -> Field -> [Rewrite a] -> Poly a -> (Poly a, Int)
normaliseCount w z rws p = -- jana narseni saldyk, birak odan da tagy birneshe ret saluga tura keledi
  let q = canonical z p
      (res, c1) = rewritesCount w z rws q
  in case res of
       Nothing -> (q, 0 + 1)
       Just r  -> let (r', c2) = normaliseCount w z rws r
                  in (r', 0 + c2 + 1)

normaliseFlag :: (Rewriting a, NFData a, NFData (Poly a)) => Weighting -> Field -> [Rewrite a] -> Poly a -> (Bool, Poly a)
normaliseFlag w z rws p = let q = canonical z p in case rewrites w z rws q of Nothing -> (True,q); Just r -> (False, normalise w z rws r)

-- Normalise a rewrite rule by a theory

normaliseRw :: (Rewriting a, NFData a, NFData (Poly a)) => Weighting -> Field -> [Rewrite a] -> Rewrite a -> Maybe (Rewrite a)
normaliseRw w z rws = snd . normaliseRwFlag w z rws

normaliseRwFlag :: (Rewriting a, NFData a, NFData (Poly a)) => Weighting -> Field -> [Rewrite a] -> Rewrite a -> (Bool, Maybe (Rewrite a))
normaliseRwFlag w z rws r = -- the whole thing depends on "rewrites"
  case rewrites w z rws (rwToPoly z r) of
    Nothing -> (True, Just r)
    Just p  ->
      let normalized = normalise w z rws p
      in (False, fmap (flip copySignature r) (polyToRw z normalized))

-- normaliseRwFlagCount :: (Rewriting a, NFData a, NFData (Poly a)) => Weighting -> Field -> [Rewrite a] -> Rewrite a -> ((Bool, Maybe (Rewrite a)), Int)
-- normaliseRwFlagCount w z rws r = -- the whole thing depends on "rewrites"
--   case rewrites w z rws (rwToPoly z r) of
--    Nothing -> ((True, Just r), 1)
--    Just p  -> let (q', c) = normaliseCount w z rws p
--               in ((False, polyToRw z q'), c + 1)

-- Normalise a set of rewrites w.r.t. itself (plus a theory)
--   Rewrites expected normal w.r.t. theory

normaliseTheory :: (Rewriting a, NFData a, NFData (Poly a)) => Weighting -> Field -> Int -> [Rewrite a] -> [Rewrite a] -> [Rewrite a]
normaliseTheory w z chunks imm mut = f mut [] where
  f []     ys = ys
  f (r:rs) ys = 
    case normaliseRw w z (imm++ys) r of
      Nothing -> f rs ys
      Just s  -> let 
                     results = map (normaliseRwFlag w z [s]) ys `using` parBuffer chunks rdeepseq
                     
                     xs = [ r' | (False, Just r') <- results ]
                     zs = [ r' | (True,  Just r') <- results ]
                 in f (xs ++ rs) (s : zs)

-- Test for indivisibility 

isNormal :: OperadTree a => [Rewrite a] -> Poly a -> Bool
isNormal rs ps = null $ catMaybes [ divide0 s (rwTree r) | r <- rs, (t,_,_) <- ps, (s,_) <- splits t ]



-- The polynomial induced by a critical pair

evaluateCP :: Rewriting a => Weighting -> Field -> CriticalPair a -> Poly a
evaluateCP w z (CP _ t pos r1 r2) = let (s,g) = splitat pos t 
                                    in fromJust (rewrite0 w z r1 t id 1)
                                         ++ map (\(x,y,i) -> (x,y,neg_ z i)) (fromJust $ rewrite0 w z r2 s g 1)

evaluateCPRw :: Rewriting a => Weighting -> Field -> CriticalPair a -> Maybe (Rewrite a)
evaluateCPRw w z cp =
  fmap (\(Rewrite t m p) -> Rewrite t m p) (polyToRw z (evaluateCP w z cp))
