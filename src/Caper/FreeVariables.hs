{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies,
        FlexibleInstances, UndecidableInstances #-}
module Caper.FreeVariables where

import qualified Data.Set as Set

class FreeVariables t v | t -> v where
        foldrFree :: (Eq v) => (v -> b -> b) -> b -> t -> b
        freeIn :: (Eq v) => v -> t -> Bool
        freeIn v = foldrFree ( (||) . (== v) ) False
        freeVariables :: (Ord v) => t -> Set.Set v
        freeVariables = foldrFree Set.insert Set.empty

instance (FreeVariables t v) => FreeVariables [t] v where
        foldrFree f = foldr (flip (foldrFree f))