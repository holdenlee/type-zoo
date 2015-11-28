{-# OPTIONS
 
 -XMultiParamTypeClasses
 -XFunctionalDependencies
 -XFlexibleInstances
 -XFlexibleContexts
 -XUndecidableInstances 
#-}

{-# LANGUAGE GeneralizedNewtypeDeriving #-}

--https://wiki.haskell.org/New_monads/MonadSupply

module MonadSupply 
    (SupplyT,
     MonadSupply,
     supply,
     peekS,
     Supply,
     evalSupplyT,
     evalSupply,
     runSupplyT,
     runSupply)
    where
import Control.Monad
import Control.Monad.Trans
import Control.Monad.Identity
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Writer
 
newtype SupplyT s m a = SupplyT (StateT [s] m a)
    deriving (Functor, Applicative, Monad, MonadTrans, MonadIO)
 
newtype Supply s a = Supply (SupplyT s Identity a)
    deriving (Functor, Applicative, Monad, MonadSupply s)
 
class Monad m => MonadSupply s m | m -> s where
    supply :: m s
    peekS :: m s
 
instance Monad m => MonadSupply s (SupplyT s m) where
    supply = SupplyT $ do
                (x:xs) <- get
                put xs
                return x
    peekS = SupplyT $ do
      (x:xs) <- get
      return x

instance (Monoid w, MonadSupply l s) => MonadSupply l (WriterT w s) where
  peekS = (lift $ peekS)
  supply = (lift $ supply)

instance (MonadSupply l s) => MonadSupply l (ReaderT r s) where
  peekS = (lift $ peekS)
  supply = (lift $ supply)

instance (MonadSupply l s) => MonadSupply l (StateT st s) where
  peekS = (lift $ peekS)
  supply = (lift $ supply)
 
evalSupplyT (SupplyT s) supp = evalStateT s supp
evalSupply (Supply s) supp = evalSupplyT s supp
 
runSupplyT (SupplyT s) supp = runStateT s supp
runSupply (Supply s) supp = runSupplyT s supp
