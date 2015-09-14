module Caper.Utils.NondetClasses where

import Control.Monad

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

        