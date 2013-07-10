{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE TypeFamilies #-}

module Interpreter where

import AST
import Parser
import Data.Map;

data Context = Map String Integer
type State = Map Integer Integer

class Eval a b where
  eval :: Context -> a -> b

instance Eval BExpr Bool where
  eval ctx (ConstBExpr _ b)                      = b
  eval ctx (NotBExpr _ e)                        = not (eval ctx e)
  eval ctx (BinaryBExpr _ And e1 e2)             = (eval ctx e1) && (eval ctx e2)
  eval ctx (BinaryBExpr _ Or e1 e2)              = (eval ctx e1) || (eval ctx e2)
--  eval ctx (RBinaryBExpr _ Equal e1 e2)          = (eval ctx e1) == (eval ctx e2)
--  eval ctx (RBinaryBExpr _ NotEqual e1 e2)       = (eval ctx e1) /= (eval ctx e2)
--  eval ctx (RBinaryBExpr _ Greater e1 e2)        = (eval ctx e1) > (eval ctx e2)
--  eval ctx (RBinaryBExpr _ Less e1 e2)           = (eval ctx e1) < (eval ctx e2)
--  eval ctx (RBinaryBExpr _ GreaterOrEqual e1 e2) = (eval ctx e1) >= (eval ctx e2)
--  eval ctx (RBinaryBExpr _ LessOrEqual e1 e2)    = (eval ctx e1) <= (eval ctx e2)

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

--instance Eval Stmt Integer where
--  eval ctx (SeqStmt _ seq)         = 0
--  eval ctx (VarStmt _ vars)        = 0
--  eval ctx (AssignStmt _ e1 e2)    = 0
--  eval ctx (ExprStmt _ e)          = 0
--  eval ctx (IfElseStmt_ b s1 s2)   = if (eval ctx b) then (eval ctx s1) else (eval ctx s2)
--  eval ctx (WhileStmt _ e s)       = 0
--  eval ctx (DoWhileStmt _ s e)     = 0
--  eval ctx (ReturnStmt _ Nothing)  = 0
--  eval ctx (ReturnStmt _ (Just e)) = 0
--  eval ctx (SkipStmt _)            = 0

--instance Eval Declr
--  type Out Declr = Maybe Integer
--  eval (Function _ n args s) = 

