{-# LANGUAGE ViewPatterns #-}

{-# OPTIONS
 
 -XFlexibleInstances
 -XMultiParamTypeClasses
#-}

module PMatch where

import Control.Monad
import qualified Data.Set as S
import qualified Data.Map as M
import Data.Maybe

import Control.Monad.Free

import Utilities
import LeafTree
import Var

pmatch' :: (Eq a, Eq v, HasVar v a) => LeafTree a -> LeafTree a -> Maybe [(v, LeafTree a)]
pmatch' t1 t2 = case (t1,t2) of
                 (Pure (getVar -> Just b), _) -> Just [(b, t2)]
                 (_, Pure (getVar -> Just b)) -> Just [(b, t1)]
                 (Pure a, _) -> if t1==t2 then Just [] else Nothing
                 (Free li1, Free li2) -> fmap concat $ sequence $ zipWith pmatch' li1 li2
                 _ -> Nothing

--Warning: only use this if you used pmatch' where only t1 or only t2 had free variables. It can't deal with multiple constraints on the same variable, like ?b = ?c -> ?d, ?b = ?e.
toSubMap :: (Eq b, Eq c, Ord b) => [(b, c)] -> Maybe (M.Map b c)
toSubMap = foldl (\m (b,c) -> m >>= (\m' -> if b `M.notMember` m' || m' M.! b == c then Just $ M.insert b c m' else Nothing)) (Just M.empty)

pmatch :: (Eq a, Eq v, Ord v, HasVar v a) => [LeafTree a] -> [LeafTree a] -> Maybe (M.Map v (LeafTree a))
pmatch = (>>= toSubMap) `c2` fmap concat `c2` sequence `c2` zipWith pmatch'

class Subbable v s where
    sub :: M.Map v s -> s -> s

--if a has variables of type v, then we can substitute with a 1-liner.
instance (Functor f, HasVar v a, Ord v) => Subbable v (Free f a) where
    sub m e = e >>= (\x -> fromMaybe (return x) (getVar x >>= (\y -> M.lookup y m)))

--the following won't be necessary for us
forward :: (Eq a, Eq b, Ord b) => [LeafTree (WithVar b a)] -> [LeafTree (WithVar b a)] ->
           LeafTree (WithVar b a) -> Maybe (LeafTree (WithVar b a))
forward li1 li2 concl = fmap (flip sub concl) (pmatch li1 li2)

backward :: (Eq a, Eq b, Ord b) => [LeafTree (WithVar b a)] -> LeafTree (WithVar b a) -> LeafTree (WithVar b a) -> Maybe [(LeafTree (WithVar b a))]
backward li c1 c2 = fmap (\x -> map (sub x) li) (pmatch [c1] [c2])
