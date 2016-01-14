{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies, RankNTypes, FlexibleInstances, UndecidableInstances #-}
module Caper.Utils.Failure where

import Control.Monad.Trans.Class
import Control.Monad.State
import Control.Monad.Reader

-- import Caper.Utils.MonadHoist


class Failure e f | f -> e where
    failure :: e -> f v
    
class (Monad m, Failure e m) => OnFailure e m where
    retry :: m a -> (e -> Maybe (m a)) -> m a
    -- ^Execute the first monadic action and the continuation; if a failure occurs
    -- pass the failure to the function; if this gives a Just, then execute that
    -- followed by the continuation; otherwise stick with the failure.

class (MonadTrans t) => FailureLift t where

instance (Failure e m, Monad m) => Failure e (StateT s m) where
    failure = lift . failure

instance (Failure e m, Monad m) => Failure e (ReaderT s m) where
    failure = lift . failure