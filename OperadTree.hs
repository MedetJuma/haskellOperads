{-# LANGUAGE LambdaCase, TypeSynonymInstances, DeriveGeneric, DeriveAnyClass #-}

module OperadTree where

import Data.Ord
import Data.List
import Data.Maybe
import Data.Ratio
import Control.Arrow
import Control.Monad
import Control.DeepSeq (NFData)
import GHC.Generics (Generic)

import Utils

-------------------------

-- Type classes for Operad Trees

class (Ord a, Arity a) => OperadTree a where
  leaf           :: Int -> a
  vertex         :: Int -> [a] -> a
  vertexS        :: Int -> Bool -> [a] -> a
  splitVertex    :: a -> Either Int ([a],[a] -> a) 
     -- Gives index of leaf / branches and root function of vertex
  
  sign_v         :: a -> Sign
  sign_t         :: a -> Sign

  depth          :: a -> Int
  vertexType     :: a -> Maybe Int
  vertexTypes    :: a -> [Int]
  leavesPaths    :: a -> ([Int],[[Int]])

  leaves         :: a -> [Int]
  minleaf        :: a -> Int
  reset          :: a -> a
  relabel        :: (Int -> Int) -> a -> a


  sign_v       = const True
  sign_t       = const True
  vertex  i    = vertexS i True
  vertexS i _  = vertex  i
  vertexType   = listToMaybe . vertexTypes



  leaves t     = case splitVertex t of
                   Left i       -> [i]
                   Right (ts,_) -> ts >>= leaves
  minleaf t    = case splitVertex t of
                   Left i -> i
                   Right (s:_,_) -> minleaf s
                   Right ( [],_) -> error "minleaf: empty vertex"
  reset t      = f (flip const) [1..] t 
                  where
                   f cc is t = case splitVertex t of
                     Left _       -> cc (tail is) . leaf $ head is
                     Right (ts,h) -> g (\js rs -> cc js (h rs)) is ts
                   g cc is = \case 
                     []     -> cc is []
                     (t:ts) -> f (\js r -> g (\ks rs -> cc ks (r:rs)) js ts ) is t


---------------

-- Signed Operad Trees

type Sign = Bool

permutationSign :: Ord a => [a] -> Sign
permutationSign = \case [] -> 0; x:xs -> permutationSign xs + (sum $ map (x<) xs)

instance Num Sign where
  (+) = (==)
  (*) = (||)

  abs = id
  signum = id
  negate = id
  fromInteger = even

---------------

-- Shuffle Operad Trees
--   trees with integer-labelled vertices of arity >0,
--   and leaves indexed by 1..n

data OT = L Int               -- L <index>
        | V Int Int [OT]      -- V <label> <depth> <branches>
        deriving (Eq,Show,Generic, NFData)

instance Ord OT where
  compare = comparing minleaf

instance Arity OT where
  arity = length . leaves

---------------

instance OperadTree OT where
  leaf        = L
  vertex i ts = V i ((1+) . maximum $ map depth ts) ts

  depth   = \case L _ ->  0;  V _ i _     -> i
  leaves  = \case L i -> [i]; V _ _ ts    -> concatMap leaves ts
  minleaf = \case L i ->  i;  V _ _ (t:_) -> minleaf t; _ -> error "minleaf: empty vertex"

  leavesPaths t = (map fst xs, map snd $ sortBy (comparing fst) xs) 
    where      xs  = f t
               f   = \case L i      -> [(i,[])]
                           V i _ ts -> ts >>= map (id *** (i:)) . f
  vertexTypes      = \case L _      -> []
                           V i _ ts -> i : (ts >>= vertexTypes)
  relabel f        = \case L i      -> L (f i)
                           V i d ts -> V i d (map (relabel f) ts)
  splitVertex      = \case L i      -> Left i
                           V i _ ts -> Right (ts, vertex i)


---------------



-- Vertices are indexed by a sign (Bool)
--   a second (Bool) stores the sign of the tree

data OTS = LS Int                      -- LS <index>
         | VS Int Bool Bool Int [OTS]  -- VS <label> <sign_v> <sign_t> <depth> <branches>
         deriving (Eq,Show,Generic, NFData)

instance Ord OTS where
  compare = comparing minleaf

instance Arity OTS where
  arity = length . leaves

forget :: OTS -> OT
forget = \case LS i -> L i;  VS i _ _ d ts -> V i d (map forget ts)

instance OperadTree OTS where
  leaf           = LS
  vertexS i b ts = VS i b (b + sum (map sign_t ts)) ((1+) . maximum $ map depth ts) ts

  depth   = \case LS _ ->  0;  VS _ _ _ d _     -> d
  leaves  = \case LS i -> [i]; VS _ _ _ _ ts    -> concatMap leaves ts
  minleaf = \case LS i ->  i;  VS _ _ _ _ (t:_) -> minleaf t; _ -> error "minleaf: empty vertex"

  leavesPaths t = (map fst xs, map snd $ sortBy (comparing fst) xs) 
    where      xs  = f t
               f   = \case LS i          -> [(i,[])]
                           VS i _ _ _ ts -> ts >>= map (id *** (i:)) . f
  vertexTypes      = \case LS _          -> []
                           VS i _ _ _ ts -> i : (ts >>= vertexTypes)
  relabel f        = \case LS i          -> LS (f i)
                           VS i b c d ts -> VS i b c d (map (relabel f) ts)
  splitVertex      = \case LS i          -> Left i
                           VS i b _ _ ts -> Right (ts, vertexS i b)

--instance Signed OTS where
  sign_v = \case LS _ -> True; VS _ b _ _ _  -> b 
  sign_t = \case LS _ -> True; VS _ _ c _ _  -> c


-------------------------

-- Asymmetric Operad Trees

data AT = LA                   -- LA <index>
        | VA Int Int Int [AT]  -- VA <label> <width> <depth> <branches>
        deriving (Eq, Show, Generic, NFData)

instance Ord AT where
  compare = comparing minleaf

instance Arity AT where
  arity = \case LA -> 1; VA _ w _ _ -> w

instance OperadTree AT where
  leaf _      = LA
  vertex i ts = VA i (sum $ map arity ts) ((1+) . maximum $ map depth ts) ts

  depth     = \case LA -> 0; VA _ _ d _  -> d
  leaves    = \case LA -> [0]; VA _ w _ _ -> replicate w 0
  minleaf _ = 0

  leavesPaths t = ([], f t)
    where        f = \case LA          -> [[]]
                           VA i _ _ ts -> ts >>= map (i:) . f
  vertexTypes      = \case LA          -> []
                           VA i _ _ ts -> (i:) $ ts >>= vertexTypes
  relabel f        = id
  splitVertex      = \case LA          -> Left 0
                           VA i _ _ ts -> Right (ts, vertex i)


-- Asymmetric Signed Trees

data ATS = LAS                              -- LAS <index>
         | VAS Int Bool Bool Int Int [ATS]  -- VAS <label> <width> <depth> <branches>
         deriving (Eq, Show, Generic, NFData)

instance Ord ATS where
  compare = comparing minleaf

instance Arity ATS where
  arity = \case LAS -> 1; VAS _ _ _ w _ _ -> w

instance OperadTree ATS where
  leaf _         = LAS
  vertexS i b ts = VAS i b (sum $ b : map sign_t ts) 
                           (sum $ map arity ts) 
                           ((1+) . maximum $ map depth ts) ts

  depth     = \case LAS ->  0;  VAS _ _ _ _ d _ -> d
  leaves    = \case LAS -> [0]; VAS _ _ _ w _ _ -> replicate w 0
  minleaf _ = 0

  leavesPaths t = ([], f t)
    where        f = \case LAS              -> [[]]
                           VAS i _ _ _ _ ts -> ts >>= map (i:) . f
  vertexTypes      = \case LAS              -> []
                           VAS i _ _ _ _ ts -> i : (ts >>= vertexTypes)
  relabel f        = id
  splitVertex      = \case LAS              -> Left 0
                           VAS i b _ _ _ ts -> Right (ts, vertexS i b)


--instance Signed ATS where
  sign_v = \case LAS -> True; VAS _ b _ _ _ _ -> b 
  sign_t = \case LAS -> True; VAS _ _ c _ _ _ -> c











