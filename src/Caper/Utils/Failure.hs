{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies, RankNTypes #-}
module Caper.Utils.Failure where

class Failure e f | f -> e where
    failure :: e -> f v
    
class (Monad m, Failure e m) => OnFailure e m where
    retry :: m a -> (e -> Maybe (m a)) -> m a
    -- ^Execute the first monadic action and the continuation; if a failure occurs
    -- pass the failure to the function; if this gives a Just, then execute that
    -- followed by the continuation; otherwise stick with the failure.
