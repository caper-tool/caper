{-# LANGUAGE GADTs #-}
{- |This module provides a monad for implementing combined angelic and
    demonic choice, with state and lazy side-effects.  Different ways
    of running this monad will execute side-effects in the underlying
    monad in different orders (perhaps even concurrently), so it is
    often important that these effects can be reordered without
    compromising the result.
-}

module Caper.Utils.Alternating where

import Control.Applicative
import Control.Monad hiding (sequence)
import Control.Monad.Trans
import Control.Monad.Trans.Maybe
import Control.Monad.Reader
import Control.Monad.State
import Caper.Utils.NondetClasses
import Caper.Utils.MonadHoist

data AlternatingT s m a where
    NoChoice :: AlternatingT s m a
    Result :: a -> AlternatingT s m a
    Lazy :: StateT s m (AlternatingT s m a) -> AlternatingT s m a
    AngelicChoice :: AlternatingT s m a -> AlternatingT s m a -> AlternatingT s m a
    DemonicChoice :: (s -> s -> s) -> AlternatingT s m a -> AlternatingT s m b -> AlternatingT s m (a, b)
    