{-# LANGUAGE DeriveDataTypeable, FlexibleInstances #-}

module Exceptions(
        module Exceptions,
        module Control.Monad.Exception)
        where
import Control.Monad.Exception

data TypeUnificationException v t = TypeUnificationException v t t
        deriving (Typeable)

instance (Show v, Show t) => Show (TypeUnificationException v t) where
        show (TypeUnificationException v t tt) =
                "The variable '" ++ show v ++
                "' cannot be both " ++ show t ++ 
                " and " ++ show tt ++ "."

instance (Show v, Show t, Typeable v, Typeable t) =>
        Exception (TypeUnificationException v t)
