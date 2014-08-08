module Caper.ExceptionContext where

import Text.ParserCombinators.Parsec

-- |The data type 'ExceptionContext' represents contextual information
-- about the cause of a 'CaperException'.
data ExceptionContext =
        StringContext String
        | SourcePosContext SourcePos
        | DescriptiveContext SourcePos String

instance Show ExceptionContext where
        show (StringContext s) = s
        show (SourcePosContext sp) = show sp
        show (DescriptiveContext sp s) = show sp ++ ": " ++ show s

class Contextual a where
        toContext :: a -> ExceptionContext
