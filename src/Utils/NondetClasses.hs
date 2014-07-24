module Utils.NondetClasses where

import Control.Monad

class MonadPlus m => MonadOrElse m where
        -- orElse: never execute the second argument
        -- if the first could succeed
        orElse :: m a -> m a -> m a

attempt :: MonadOrElse m => m () -> m ()
-- Do the action if possible
attempt a = orElse a (return ())
