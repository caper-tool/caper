{-# LANGUAGE FlexibleInstances #-}
module Caper.ExceptionContext where

import Text.ParserCombinators.Parsec
import Control.Lens -- XXX: I feel a little bad about this lens being a dependency of the parser

-- |The data type 'ExceptionContext' represents contextual information
-- about the cause of a 'CaperException'.
data ExceptionContext =
        StringContext String
        | SourcePosContext SourcePos
        | DescriptiveContext SourcePos String

instance Show ExceptionContext where
        show (StringContext s) = s
        show (SourcePosContext sp) = show sp
        show (DescriptiveContext sp s) = show sp ++ ": " ++ s

class Contextual a where
        toContext :: a -> ExceptionContext
instance Contextual ExceptionContext where
        toContext = id
instance Contextual String where
        toContext = StringContext
class ECLenses c where
        exceptionContext :: Simple Lens c [ExceptionContext] 
instance ECLenses [ExceptionContext] where
        exceptionContext = lens id (\_ y -> y)