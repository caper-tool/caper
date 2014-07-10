{-# LANGUAGE DeriveDataTypeable #-}
import Data.Generics

data Frob a = Plig a a | Plog a Int deriving (Typeable, Data)


