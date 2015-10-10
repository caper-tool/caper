{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
module Caper.Utils.NondetClasses where

import Control.Monad
import Control.Monad.State

import Caper.Utils.MonadHoist

class MonadPlus m => MonadOrElse m where
        -- orElse: never execute the second argument
        -- if the first could succeed
        orElse :: m a -> m a -> m a

attempt :: MonadOrElse m => m () -> m ()
-- Do the action if possible
attempt a = orElse a (return ())

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
        