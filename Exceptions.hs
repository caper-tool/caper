{-# LANGUAGE DeriveDataTypeable, FlexibleInstances #-}

module Exceptions(
        module Exceptions,
        module Control.Monad.Exception)
        where
import Control.Monad.Exception

data TypeUnificationException v t = TypeUnificationException v t t
        | TypeUnificationException2 v t v t
        deriving (Typeable)

instance (Show v, Show t) => Show (TypeUnificationException v t) where
        show (TypeUnificationException v t tt) =
                "The variable '" ++ show v ++
                "' cannot be both " ++ show t ++ 
                " and " ++ show tt ++ "."
        show (TypeUnificationException2 v1 t1 v2 t2) =
                "The variables '" ++ show v1 ++
                "' (of type " ++ show t1 ++
                ") and '" ++ show v2 ++
                "' (of type " ++ show t2 ++
                ") are required to have the same type."

instance (Show v, Show t, Typeable v, Typeable t) =>
        Exception (TypeUnificationException v t)
