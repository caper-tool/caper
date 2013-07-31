{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE TypeFamilies #-}

module Interpreter where

import AST
import Parser
import Control.Monad.State
import Data.Map (Map)
import qualified Data.Map as Map

type Context = Map String Integer
type Heap = Map Integer Integer

type StateM = StateT Heap IO

data StmtValue = NormalValue Integer
               | ReturnValue Integer

class Eval a b where
  eval :: Context -> a -> b

instance Eval BExpr Bool where
  eval ctx (ConstBExpr _ b)                      = b
  eval ctx (NotBExpr _ e)                        = not (eval ctx e)
  eval ctx (BinaryBExpr _ And e1 e2)             = (eval ctx e1) && (eval ctx e2)
  eval ctx (BinaryBExpr _ Or e1 e2)              = (eval ctx e1) || (eval ctx e2)
  eval ctx (RBinaryBExpr _ Equal e1 e2)          = ((eval :: Context -> AExpr -> Integer) ctx e1) == ((eval :: Context -> AExpr -> Integer) ctx e2)
  eval ctx (RBinaryBExpr _ NotEqual e1 e2)       = ((eval :: Context -> AExpr -> Integer) ctx e1) /= ((eval :: Context -> AExpr -> Integer) ctx e2)
  eval ctx (RBinaryBExpr _ Greater e1 e2)        = ((eval :: Context -> AExpr -> Integer) ctx e1) > ((eval :: Context -> AExpr -> Integer) ctx e2)
  eval ctx (RBinaryBExpr _ Less e1 e2)           = ((eval :: Context -> AExpr -> Integer) ctx e1) < ((eval :: Context -> AExpr -> Integer) ctx e2)
  eval ctx (RBinaryBExpr _ GreaterOrEqual e1 e2) = ((eval :: Context -> AExpr -> Integer) ctx e1) >= ((eval :: Context -> AExpr -> Integer) ctx e2)
  eval ctx (RBinaryBExpr _ LessOrEqual e1 e2)    = ((eval :: Context -> AExpr -> Integer) ctx e1) <= ((eval :: Context -> AExpr -> Integer) ctx e2)

instance Eval AExpr Integer where
  eval ctx (VarAExpr _  n)                = 0
  eval ctx (DerefAExpr _ e)               = eval ctx e
  eval _ (ConstAExpr _ i)                 = i
  eval ctx (NegAExpr _ e)                 = - (eval ctx e)
  eval ctx (BinaryAExpr _ Add e1 e2)      = (eval ctx e1) + (eval ctx e2)
  eval ctx (BinaryAExpr _ Subtract e1 e2) = (eval ctx e1) - (eval ctx e2)
  eval ctx (BinaryAExpr _ Multiply e1 e2) = (eval ctx e1) * (eval ctx e2)
  eval ctx (BinaryAExpr _ Divide e1 e2)   = quot (eval ctx e1) (eval ctx e2)
  eval ctx (CallAExpr _ n args)           = 0

instance Eval Stmt StmtValue where
  eval ctx (SeqStmt _ seq)         = NormalValue 0
  eval ctx (VarStmt _ vars)        = NormalValue 0
  eval ctx (AssignStmt _ e1 e2)    = NormalValue 0
  eval ctx (ExprStmt _ e)          = NormalValue (eval ctx e)
  eval ctx (IfElseStmt _ b s1 s2)  = if (eval ctx b) then (eval ctx s1) else (eval ctx s2)
  eval ctx (WhileStmt _ _ e s)     = NormalValue 0
  eval ctx (DoWhileStmt _ _ s e)   = NormalValue 0
  eval ctx (ReturnStmt _ Nothing)  = ReturnValue 0
  eval ctx (ReturnStmt _ (Just e)) = ReturnValue (eval ctx e)
  eval ctx (SkipStmt _)            = NormalValue 0
