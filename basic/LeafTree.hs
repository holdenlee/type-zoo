{-# OPTIONS

 -XFlexibleInstances
 -XFunctionalDependencies
 -XMultiParamTypeClasses
 -XTypeSynonymInstances
 
#-}

module LeafTree where

import Control.Monad.Free

type LeafTree = Free [] 

leaf = Pure
node = Free

class IsLeafTree s a | a -> s where
    toLeafTree :: a -> LeafTree s
    fromLeafTree :: LeafTree s -> a

instance IsLeafTree a (LeafTree a) where
    toLeafTree = id
    fromLeafTree = id

--Any datatype that looks like a list of a's allows easy conversion to and from lists; the free monad then allows easy conversion to and from leaftrees.
class Listlike f where
    toL :: f a -> ([String], [a])
    fromL :: [LeafTree String] -> f (LeafTree String)

instance (Functor f, Listlike f) => IsLeafTree String (Free f String) where
    toLeafTree (Free e) = case toL e of
                            (li, as) -> Free ((map Pure li)++(map toLeafTree as))
    toLeafTree (Pure a) = Pure a
    fromLeafTree lt = case lt of
                        Pure a -> Pure a
                        Free li -> Free $ fmap fromLeafTree $ fromL li
