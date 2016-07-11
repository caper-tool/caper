{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
module Caper.Utils.NondetClasses where

import Data.Foldable
import Control.Monad hiding (msum)
import Control.Monad.State hiding (msum)
import Control.Applicative

import Caper.Utils.MonadHoist

class MonadPlus m => MonadOrElse m where
        -- orElse: never execute the second argument
        -- if the first could succeed
        orElse :: m a -> m a -> m a

attempt :: MonadOrElse m => m () -> m ()
-- Do the action if possible
attempt a = orElse a (return ())

instance (MonadPlus m, MonadOrElse m) => MonadOrElse (StateT s m) where
    orElse (StateT a) (StateT b) = StateT $ \s -> a s `orElse` b s 

class MonadPlus m => MonadCut m where
        -- |Prevent rolling back after computing any witness.
        cut :: m a -> m a
        cut = (>>= \x -> cut_ >> return x)
        -- |Do not roll back the computation from this point.
        -- This is useful if the non-deterministic choices made so far cannot affect the future.
        cut_ :: m ()
        cut_ = cut (return ())

instance (MonadPlus m, MonadCut m) => MonadCut (StateT s m) where
        cut = hoist cut

class Monad m => MonadDemonic m where
        (<#>) :: m a -> m a -> m a
        succeed :: m a

-- |Demonic choice on all items of a list.
-- Only really makes sense if the list is non-empty.
dAll :: MonadDemonic m => [m a] -> m ()
dAll [] = succeed
dAll [a] = a >> return ()
dAll (a:aa) = (a >> return ()) <#> dAll aa

instance (MonadDemonic m) => MonadDemonic (StateT s m) where
        (StateT a) <#> (StateT b) = StateT (\s -> a s <#> b s)
        succeed = lift succeed

-- |Lift a 'Maybe' into an arbitrary non-deterministic monad.
liftMaybe :: (MonadPlus m) => Maybe a -> m a
liftMaybe (Just x) = return x
liftMaybe Nothing = mzero

chooseFrom :: (Functor t, Foldable t, MonadPlus m) => t a -> m a
chooseFrom = msum . fmap return

class (Monad m) => MonadLabel m where
        label :: String -> m ()

instance (MonadLabel m) => MonadLabel (StateT s m) where
        label = lift . label

{-
{- |Record the current state; execute the first computation; revert to the saved state;
    execute the second computation.  
-} 
branch :: (MonadState s m, MonadCut m) => m a -> m b -> m (a, b)
branch b1 b2 = do
                s <- get
                r1 <- b1
                put s
                cut_
                r2 <- b2
                put $ error "State is invalid after a branch"
                return (r1, r2)

{- |Like 'branch', but throws away the results of the computations.
-}
branch_ :: (MonadState s m, MonadCut m) => m a -> m b -> m ()
branch_ b1 b2 = branch b1 b2 >> return ()

branches :: (MonadState s m, MonadCut m) => [m a] -> m [a]
branches [] = return []
branches [a] = a >>= (return . (:[]))
branches (a:aa) = do
        (b,bb) <- branch a (branches aa)
        return (b:bb)

branches_ :: (MonadState s m, MonadCut m) => [m a] -> m ()
branches_ [] = return ()
branches_ [a] = a >> return ()
branches_ (a:aa) = branch_ a (branches_ aa)
    -}    
