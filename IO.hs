{-# LANGUAGE LambdaCase, FlexibleInstances, TypeSynonymInstances, RankNTypes #-}

module IO where

import Control.Monad
import Data.Ord
import Data.List
import Data.Maybe
import Text.Printf
import System.Timeout
import System.CPUTime
import Control.DeepSeq
import Control.Parallel.Strategies

import Utils
import Signature
import OperadTree
import Operations
import Generation
import Polynomials
import Measure
import CriticalPairs
import Rewriting
import PrettyPrinting


-- KNUTH-BENDIX / BUCHBERGER

data Stage a = Stage {size          :: Int,
                      signature     :: Signature,
                      weights       :: Weighting,
                      stable        :: [Rewrite a],
                      small         :: [CriticalPair a],
                      large         :: [CriticalPair a],
                      currentMaxIdx :: Int
                      }

instance Arity (Stage a) where
  arity = size

printSizes :: String -> Stage a -> IO ()
printSizes tag st = putStrLn $ tag ++ ": arity=" ++ show (arity st)
                                   ++ " small=" ++ show (length $ small st)
                                   ++ " large=" ++ show (length $ large st)

printOpCounts :: String -> Int -> Int -> Int -> Int -> IO ()
printOpCounts tag evalCount normCount theoryCount relCpCount = putStrLn $ tag ++ ": evaluateCP=" ++ show evalCount
                                                   ++ " normalise=" ++ show normCount
                                                   ++ " normaliseTheory=" ++ show theoryCount
                                                   ++ " relativeCPs=" ++ show relCpCount

----------


type THEORY = Either (Either [Poly OT] [Poly OTS]) (Either [Poly AT] [Poly ATS])

data Config = Config {doNormalise    :: Bool,
                      doCount        :: Bool,
                      doStageCount   :: Bool,
                      countArity     :: Int,
                      breakArity     :: Maybe Int,
                      breakTime      :: Maybe Int,
                      printInit      :: Bool,
                      printNew       :: Bool,
                      printFinal     :: Bool,
                      printCPs       :: Bool,
                      getField       :: Field,
                      getMeasure     :: Measure,
                      getSignature   :: Signature,
                      getTheory      :: THEORY,
                      getReduce      :: Maybe THEORY
                     }

isLeft = \case Left _ -> True; Right _ -> False
isShuffle = isLeft . getTheory
isSigned  = not . (\case Left x -> isLeft x; Right x -> isLeft x) . getTheory


instance Show Config where
  show x =
    let a = "\n\nConfiguration:\n"
        b = "actions:        " ++ (if doNormalise x then "normalise " else "")
                               ++ (if doCount x then "count " else "")
                               ++ (if doStageCount x then "stageCount " else "")
        c = "count limit:    " ++ show (countArity x)
        d = "arity limit:    " ++ case breakArity x of Just i -> show i; Nothing -> "none"
        e = "time limit:     " ++ case breakTime  x of Just i -> showTime i; Nothing -> "none"
        f = "output:         " ++ intercalate "\n                " (mapMaybe id [
                                   if printInit  x then Just "initial theory" else Nothing, 
                                   if printNew   x then Just "newly stable rewrite rules" else Nothing,
                                   if printFinal x then Just "final theory" else Nothing,
                                   if printCPs   x then Just "evaluation of critical pairs" else Nothing ])
        g = "field:          " ++ case getField x of Nothing -> "rationals"; Just i -> "integers up to " ++ show i 
        h = "operad type:    " ++ (if isSigned   x then "signed "  else "unsigned ")
                               ++ (if isShuffle  x then "shuffle " else "asymmetric ") ++ "operad"
        i = "measure:        " ++ showMeasure (getMeasure x)
        j = "signature:      " ++ (intercalate " " . map show $ getSignature x)    
        k = "theory:\n\n  "    ++ intercalate "\n\n  " l 
        l = case getTheory x of Left  (Left  t) -> map (pp $ getSignature x) t
                                Left  (Right t) -> map (pp $ getSignature x) t
                                Right (Left  t) -> map (pp $ getSignature x) t
                                Right (Right t) -> map (pp $ getSignature x) t
        reduceText = \case
          Left  (Left  t) -> intercalate "\n\n  " (map (pp $ getSignature x) t)
          Left  (Right t) -> intercalate "\n\n  " (map (pp $ getSignature x) t)
          Right (Left  t) -> intercalate "\n\n  " (map (pp $ getSignature x) t)
          Right (Right t) -> intercalate "\n\n  " (map (pp $ getSignature x) t)
        mText = maybe "" (\r -> "reduce:\n\n  " ++ reduceText r) (getReduce x)
      in unlines [a,b,c,d,e,f,g,h,i,j,k,mText]

showTime t = let h = div t 3600
                 m = rem t 3600 `div` 60
                 s = rem t 60
             in if all (==0) [h,m,s] then "0s" else
                  (if h==0 then "" else show h ++ "h ") ++
                  (if m==0 then "" else show m ++ "m ") ++
                  (if s==0 then "" else show s ++ "s ")


----------

-- rewrite theory + printing 
initialise :: (Rewriting a, PPrint a, NFData a, NFData (Poly a)) => Config -> [Poly a] -> IO (Stage a)
initialise cfg ps = -- maybe it's possible to just pass ps or just cfg?
  let sig = getSignature cfg
      w   = weighting sig
      -- rws = rewritten rules (rewrites)
      rws = zipWith assignInitialSignature [1..]
            $ normaliseTheory w (getField cfg) [] (mapMaybe (polyToRw $ getField cfg) ps)
      -- lrg = large queued critical pairs
      lrg = selfCPs rws
      currentMaxIdx = length rws
      str = "Initial rewrite theory:\n\n  " ++ pp sig rws
  in do if printInit cfg then putStrLn str else return ()
        return (Stage 0 sig w rws [] lrg currentMaxIdx)
  where
    assignInitialSignature i (Rewrite t m p _ _) = Rewrite t m p (znleaves (arity t), m, 1) i


-- berilgen polynomdardy ulken kishi dep bolu.
stepCP :: (Rewriting a, PPrint a) => Stage a -> IO (Stage a)
stepCP (Stage i sig w sta [] cps currentMaxIdx) =
  putStrLn str >> printSizes "stepCP" st' >> return st'
  where
    n = if null cps then i else minimum (map arity cps)
    (sml,lrg) = partition ((==n) . arity) cps -- if arity is greater than n, it's large 
    str = "\nArity: " ++ show n ++
      "   Stable rewrite rules: "   ++ show (length sta) ++
      "   Current critical pairs: " ++ show (length sml) ++ -- sml = small (current)
      "   Queued critical pairs: "  ++ show (length lrg) ++ "\n"
    st' = Stage n sig w sta sml lrg currentMaxIdx


-- barlyk esepteuler osynda
stepNM :: (Rewriting a, PPrint a, NFData a) => Config -> Stage a -> IO (Stage a)
stepNM cfg (Stage i sig w sta sml lrg currentMaxIdx) =
  let z   = getField cfg
      -- 1. Evaluate and normalise in parallel 

      rawNor = (map (\cp -> evaluateCPRw w z cp >>= normaliseRw w z sta) sml) `using` parListChunk 16 rdeepseq
      nor = catMaybes rawNor

      -- 2. Normalise theory
      rawNew = normaliseTheory w z sta nor
      
      -- 3. Reindex new rules
      nextIdx = currentMaxIdx + 1

      -- new = if nextIdx <= 300
      --   then let sortedRawNew = sortBy (comparing (\(Rewrite _ _ _ _ sigL) -> sigL)) rawNew
      --        in zipWith reindexRule [nextIdx..] sortedRawNew `using` parListChunk 16 rseq
      --   else rawNew
      
      -- sortedRawNew = sortBy (comparing (\(Rewrite _ _ _ _ sigL) -> sigL)) rawNew 
          
      -- Evaluate the reindexing in parallel chunks
      new = zipWith reindexRule [nextIdx..] rawNew `using` parListChunk 16 rseq
      newMaxIdx = currentMaxIdx + length new
      
      -- 4. Find relative CPs using the newly indexed rules
      rawCPs = relativeCPs sta new ++ selfCPs new
      
      -- 5. Filtering with respect to Buchberger's triangle lemma
      keepMask = map (not . isRedundant (sta ++ new)) rawCPs `using` parListChunk 16 rseq
      triangleCPs = [ cp | (cp, True) <- zip rawCPs keepMask ]
      -- cps = rawCPs

      -- 6. Filtering with respect to F5 
      -- keepMaskF = map (not . isRedundantF5 (sta ++ new)) triangleCPs `using` parListChunk 16 rseq
      -- cps = [ cp | (cp, True) <- zip triangleCPs keepMaskF ]
      cps = triangleCPs

      str1 = if null new then "No new rewrite rules\n"
                         else "Newly stable rewrite rules:\n\n  " ++ intercalate "\n\n  " (map (pp sig) new)
      str2 = unlines $ zipWith f sml nor
      f s1 s2 = pp sig s1 ++ "\n    resolves to:\n" ++ pp sig s2 ++ "\n"
  in do
    if printNew cfg then putStrLn str1 else return ()
    if printCPs cfg then putStrLn str2 else return ()

    -- Append the correctly indexed new rules to the stable basis
    return $ Stage i sig w (sta ++ new) [] (lrg ++ cps) newMaxIdx
  where
    reindexRule j (Rewrite t m p sigM _) = Rewrite t m p sigM j

-- stepNM :: (Rewriting a, PPrint a, Eq a) => Config -> Stage a -> IO (Stage a)
-- stepNM cfg (Stage i sig w sta sml lrg) = -- Buchberger algorithm step
--   let z   = getField cfg
--       -- evaluateCP is computing the S polynomials
--       -- evaluateCP -> S-polynomdardy esepteu (~ 100 operations)
--       -- normalise -> polynomdar jyinyn kyskartu (~10 ^ 4 operations)
--       processCPs [] evalOps normOps = ([], evalOps, normOps)
--       processCPs (cp:cps') evalOps normOps =
--         let (poly', evalOps1) = evaluateCPCount w z cp
--             (poly'', normOps1) = normaliseCount w z sta poly'
--             (rest, evalOps', normOps') = processCPs cps' (evalOps + evalOps1) (normOps + normOps1)
--         in (poly'' : rest, evalOps', normOps')
--       activeSml = filter (not . isRedundant sta) sml
--       (nor, evalCount, normaliseOps) = processCPs activeSml 0 0
--       (new, normaliseTheoryOps) = normaliseTheoryCount w z sta $ mapMaybe (polyToRw z) nor
--       (relativeCps, relativeCpCount) = relativeCPsCount sta new
--       rawCPs = relativeCps ++ selfCPs new
--       -- filter redundant critical pairs according to Buchberger's triangle lemma
--       cps = filter (not . isRedundant (sta ++ new)) rawCPs
--       diagRedundant = length sml - length activeSml
--       diagQueue = length rawCPs - length cps
--       str1 = if null new then "No new rewrite rules\n"
--                          else "Newly stable rewrite rules:\n\n  " ++ intercalate "\n\n  " (map (pp sig) new)
--       str2 = unlines $ zipWith f sml nor
--       f s1 s2 = pp sig s1 ++ "\n    resolves to:\n" ++ pp sig s2 ++ "\n"
--       st' = Stage i sig w (sortBy (comparing (\(_,_,p) -> length p)) $ sta ++ new) [] (lrg ++ cps)
--   in do if printNew cfg then putStrLn str1 else return ()
--         if printCPs cfg then putStrLn str2 else return ()
--         printOpCounts "stepNM" evalCount normaliseOps normaliseTheoryOps relativeCpCount
--         putStrLn $ "  [redundancy filter: " ++ show diagRedundant ++ " small filtered, " ++ show diagQueue ++ " queued filtered]"
--         printSizes "stepNM" st' >> return st'


stop :: (Rewriting a, PPrint a) => Config -> Stage a -> Maybe String
stop cfg st | null (small st) && null (large st) = --naturally if small and large are null, we stop
                Just ("Success!" 
                      -- ++ if printFinal cfg then " Complete theory: \n\n  " ++ pp (signature st) (stable st) else "" )
                      ++ if printFinal cfg then " Complete theory: \n\n  " ++ pp (signature st) (stable st) else "" )
            | Just i <- breakArity cfg, arity st >= i = 
                Just ("Stopped at arity " ++ show (arity st) ++ "."
                      ++ if printFinal cfg then " Theory thus far: \n\n  " ++ pp (signature st) (stable st) else "" )
            | otherwise = Nothing


loop :: (Rewriting a, PPrint a, NFData a, NFData (Poly a), Memoizable a) => Config -> Stage a -> IO (Stage a)
loop cfg st = case stop cfg st of
                Nothing  -> do
                  st' <- stepCP st >>= stepNM cfg
                  if doStageCount cfg 
                     then generate (isShuffle cfg) (arity st') st'
                     else return ()
                  loop cfg st'
                Just str -> putStrLn str >> return st

timedLoop :: (Rewriting a, PPrint a, NFData a, NFData (Poly a), Memoizable a) => Config -> Integer -> Stage a -> IO (Stage a)
timedLoop cfg t1 st = 
  let str = ("Timed out at arity " ++ show (arity st) ++ "." ++ 
             if printFinal cfg then " Theory thus far: \n\n" ++ pp (signature st) (stable st) else "")
  in case stop cfg st of
       Just str -> putStrLn str >> return st
       Nothing  -> do t0 <- getCPUTime
                      let d = fromIntegral $ div (t1 - t0) (10^6)
                      if d <= 0 then putStrLn str >> return st
                                else do m  <- timeout d (stepCP st >>= stepNM cfg)
                                        case m of 
                                          Nothing  -> putStrLn str >> return st
                                          Just st' -> do
                                            if doStageCount cfg 
                                               then generate (isShuffle cfg) (arity st') st'
                                               else return ()
                                            timedLoop cfg t1 st'
  

solve_ :: (Rewriting a, PPrint a, NFData a, NFData (Poly a), Eq a, Memoizable a) => Config -> Maybe [Poly a] -> [Poly a] -> IO ()
-- cfg = configurations
-- st = stage (groebner basis so far)
-- ps = polynomials
solve_ cfg mReduce ps = do
  st0 <- initialise cfg ps -- initialise configurations and polynomials
  stn <- if doNormalise cfg
         then case breakTime cfg of
                Nothing -> loop cfg st0
                Just i  -> do t0 <- getCPUTime
                              timedLoop cfg (t0 + (fromIntegral i * 10^12)) st0
         else return st0
  case mReduce of
    Nothing -> return ()
    Just rs -> do
      let sig = signature stn
          w   = weights stn
          z   = getField cfg
          reducePoly p = reduceByTheory w z (stable stn) p
          pairs = zip rs (map reducePoly rs)
      putStrLn "\nReduced tree(s):\n"
      putStrLn $ intercalate "\n\n" [ "  " ++ pp sig p ++ "\n    ->  " ++ pp sig q | (p,q) <- pairs ]
  if doCount cfg -- doCount is a Boolean in Configuration cfg
  then generate (isShuffle cfg) (countArity cfg) stn -- count normal forms
  else return ()

reduceByTheory :: (Rewriting a, Eq a) => Weighting -> Field -> [Rewrite a] -> Poly a -> Poly a
reduceByTheory w z rws p =
  let nf = normalise w z rws p
  in if nf /= canonical z p
        then negatePoly z nf
   else case p of
     [(t,_,_)] -> maybe nf (negatePoly z) (solveRuleForTree z t rws)
     _         -> nf

negatePoly :: Field -> Poly a -> Poly a
negatePoly z = map (\(t,m,i) -> (t,m,neg_ z i))

solveRuleForTree :: (OperadTree a, Eq a) => Field -> a -> [Rewrite a] -> Maybe (Poly a)
solveRuleForTree z target rws = listToMaybe $ mapMaybe (isolateTarget z target . rwToPoly z) rws

isolateTarget :: Eq a => Field -> a -> Poly a -> Maybe (Poly a)
isolateTarget z target poly = do
  (_, _, coeff) <- find ((== target) . fromMono) poly
  let others = [ (t, m, mul_ z (neg_ z 1) (div_ z c coeff))
               | (t, m, c) <- poly
               , t /= target ]
  return (canonical z others)

solve :: Config -> IO ()
solve cfg = case (getTheory cfg, getReduce cfg) of
              (Left  (Left  t), r) -> solve_ cfg (matchReduceOT  r) t
              (Left  (Right t), r) -> solve_ cfg (matchReduceOTS r) t
              (Right (Left  t), r) -> solve_ cfg (matchReduceAT  r) t
              (Right (Right t), r) -> solve_ cfg (matchReduceATS r) t

matchReduceOT :: Maybe THEORY -> Maybe [Poly OT]
matchReduceOT = \case
  Nothing -> Nothing
  Just (Left (Left t)) -> Just t
  _ -> Nothing

matchReduceOTS :: Maybe THEORY -> Maybe [Poly OTS]
matchReduceOTS = \case
  Nothing -> Nothing
  Just (Left (Right t)) -> Just t
  _ -> Nothing

matchReduceAT :: Maybe THEORY -> Maybe [Poly AT]
matchReduceAT = \case
  Nothing -> Nothing
  Just (Right (Left t)) -> Just t
  _ -> Nothing

matchReduceATS :: Maybe THEORY -> Maybe [Poly ATS]
matchReduceATS = \case
  Nothing -> Nothing
  Just (Right (Right t)) -> Just t
  _ -> Nothing

generate :: (Rewriting a, PPrint a, NFData a, Memoizable a) => Bool -> Int -> Stage a -> IO ()
generate b i st = --(b -> Shuffle or not), (i -> count arity), (st) -> Groebner basis
  do putStrLn "\nCounting normal forms:\n\n  arity | normal forms"
     if b then write $ normalShuffleTreesUpto (signature st) ts i
          else write $ normalTreesUpto (signature st) ts i
  where ts = map rwTree $ stable st
        write xs = putStrLn $ unlines [ write1 nn | nn <- zip [3..] . map length $ drop 3 xs ]
        write1 (i,n) = align 6 (show i) ++ "  | " ++ align 7 (show n) 
        align n str  = replicate (n - length str) ' ' ++ str
       
