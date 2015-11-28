{-# OPTIONS

 -XFlexibleContexts
 -XFlexibleInstances
 -XFunctionalDependencies
 -XMultiParamTypeClasses
 -XUndecidableInstances

#-}

--module HindleyMilner where
module Main where

import Control.Arrow
import Control.Lens hiding (set)
import Data.Char
import Data.List
import qualified Data.Map.Strict as M
import Data.Maybe
import qualified Data.Set as S
import Data.Foldable
import Data.Traversable
import Control.Monad.Free
import Control.Monad.State
import Control.Monad.Trans
import Control.Monad.Identity
import Control.Monad.Trans.Reader
--import Control.Monad.Trans.State
import Control.Monad.Trans.Writer

import MonadSupply
import LeafTree
import Parser
import PMatch
import Utilities
import Var

--Infer Monad
type Infer' s w sup a = ReaderT s (WriterT w (Supply sup)) a
type Infer a = Infer' Typing [(Type', Type')] String a

--Expressions
data ExprBuilder v a = Let v a a | Fun v a | App [a] deriving Show
type Expr v = Free (ExprBuilder v)
type Expr' = Expr String String

--Types
type Type' = LeafTree String
data Polytype = Forall (S.Set String) Type'

--ExprBuilder instances. Note this makes (Expr v = Free (ExprBuilder v)) automatically foldable, traversable, and functor.
instance Traversable (ExprBuilder v) where 
    traverse f e = case e of
                     Let v a1 a2 -> Let v <$> f a1 <*> f a2
                     Fun v a -> Fun v <$> f a
                     App li -> App <$> (sequenceA $ map f li)

instance Foldable (ExprBuilder v) where
    foldMap =  foldMapDefault

instance Functor (ExprBuilder v) where 
    fmap = fmapDefault

instance Listlike (ExprBuilder String) where
    toL e = case e of
              Let v a1 a2 -> (["let", v], [a1, a2])
              Fun v a -> (["fun", v], [a])
              App li -> ([], li)
    fromL li = case li of 
                [Pure "let", Pure v, a1, a2] -> Let v a1 a2
                [Pure "fun", Pure v, a] -> Fun v a
                li -> App li

comp :: (Subbable v s, Ord v) => M.Map v s -> M.Map v s -> M.Map v s
comp m2 m1 = (M.map (sub m2) m1) `M.union` m2
--m1 is first. then m2

--substitution
type Typing = M.Map String Polytype

{-|
  In Infer, 
  * keep track of Typing: map from variables to polytpes
  * list of generated constraints
  * keep a fresh supply of variables (strings)
  a is the variable representing the current type.
-}

--mapM :: Monad m => (a -> m b) -> t a -> m (t b)
--can generalize this...
--free type variables
--this is a little hacky right now, relying on all lowercase things to be type variables. After changing this, I should possibly change generalize to depend on environment
ftv :: Type' -> S.Set String
ftv t = S.fromList $ filter (\x -> isLower (x!!0)) $ toList t

--can put Type' and Polytype in same class...
fptv :: Polytype -> S.Set String
fptv (Forall s t) = (ftv t) S.\\ s

generalize :: Type' -> Polytype
generalize s = Forall (ftv s) s

fun x y = Free [Pure "Fun", x, y]
set x = Free [Pure "Set", x]

--Note that it infers a Type', not a Polytype. We will close over afterwards. (Why not just return Polytype?)
getConstraints :: Expr' -> Infer Type'
getConstraints expr = 
    case expr of
      Free (Let x e1 e2) ->  
          do
            --generate a fresh type variable for the type of the expression
            a <- supply
            --solve the constraints in e1
            a1 <- getConstraints e1 
            --close over all free type variables (i.e., if x is free, add "forall x." at beginning. Let bindings are maximally generalized.
            let a1' = generalize a1
            --what we want to do here is to add the constraint x::a1, solve for the constraints in e2, and then remove the constraint x::a1 (because we'll go back up the expression tree, and x::a1 doesn't make sense outside the scope of let). Reader gives us a function to do exactly this, local :: (r -> r) -> m a -> m a
            a2 <- local (M.insert x a1') (getConstraints e2)
            --generate a constraint: a ~ a2
            lift $ tell [(Pure a, a2)]
            return (Pure a)
      Free (Fun x e) -> 
          do
            --generate a fresh type variable for the type of x
            a <- supply 
            --with the fact that x::a to the map, solve the constraints for e, given that x::a. Note that we turn a into a Polytype. The (only) variable a is free.
            b <- local (M.insert x (Forall S.empty (Pure a))) (getConstraints e)
            --the type is "a -> b"
            return (fun (Pure a) b)
      Free (App (f:rest)) -> 
          do
            --let b be the type of the expression
            b <- supply
            --get the type of f
            a <- getConstraints f
            --get the types of each argument in rest
            as <- mapM getConstraints rest
            --the type of a is a1 -> ... -> al -> b, and the resulting type of the expression is b
            lift $ tell [(a, foldr1 fun (as++[Pure b]))]
            return (Pure b)
      Pure x -> 
          do
            subst <- ask
            --if it's not found, there's an error. TODO: add error handling. TODO: allow a function to look up, not just a substitution.
            --for every variable in "forall", instantiate with fresh type variable
            let b = fromJust (M.lookup x subst)
            b' <- lift $ lift $ instantiate b
            return b'

instantiate :: Polytype -> Supply String Type'
instantiate t = do
  --get all the bound variables (NOT the free ones. how many of them are there?
  let Forall bds ty = t
  let tvs = S.toList bds
  let s = length tvs
  --now get generate a fresh variable for each
  as <- sequence $ replicate s supply
  --make a map from the old to the new
  let m = M.fromList $ zip tvs (map Pure as)
  --and substitute!
  return $ sub m ty

li1 = [("id", generalize $ fun (Pure "a") (Pure "a")),
       ("single", generalize $ fun (Pure "a") (set (Pure "a"))), 
       ("1", generalize $ Pure "Int")]

main = do
  let expr = parseE "(single (let x id (x id 1)))" :: Expr'
  --print expr
  let subst = M.fromList li1
  let (t, w) = runIdentity $ evalSupply (runWriterT $ runReaderT (getConstraints expr) (subst)) (map (('x':).show) [1..]) -- need to make sure this isn't used
  prettyList w
  let s = evalState solve (M.empty, w)
  putStrLn $ pretty $ sub s t

printList :: (Show a) => [a] -> IO ()
printList = mapM_ (putStrLn . show)

prettyList :: (Pretty a) => [a] -> IO ()
prettyList = mapM_ (putStrLn . pretty)

class Pretty a where
    pretty :: a -> String

instance Pretty String where
    pretty = id

instance Pretty Type' where
    pretty t = case t of
                 Pure a -> a
                 Free [Pure "Fun", x, y] -> "("++(pretty x)++" -> "++(pretty y)++")"
                 Free li -> "("++(intercalate " " $ map pretty li)++")"

instance Pretty a => Pretty (a, a) where
    pretty (x, y) = (pretty x)++" ~ "++(pretty y)

--don't really need this to be in state monad - but will presumably be easier once I add Except, etc. 
solve :: State (M.Map String Type', [(Type', Type')]) (M.Map String Type')
solve = do
  (m, cs) <- get
  case cs of
    [] -> return m
    (h1, h2):rest -> do
            --no error handling. [(String, LeafTree String)]
            let h:rest' = fromJust $ pmatch' h1 h2
            let rest'' = (map (first Pure) rest')++rest
            let m2 = M.fromList [h]
            let rest''' = map (both %~ sub m2) rest''
            let m' = m `comp` m2
            put (m', rest''')
            solve
