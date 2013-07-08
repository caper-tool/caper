{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE TypeFamilies #-}

module Interpreter where

import Parser

class Eval a where
  type Out a :: *
  eval :: a -> Out a

instance Eval BExpr where
  type Out BExpr = Bool
  eval (BoolConst _ b)                  = b
  eval (Not _ e)                        = not $ eval e
  eval (BBinary _ And e1 e2)            = (eval e1) && (eval e2)
  eval (BBinary _ Or e1 e2)             = (eval e1) || (eval e2)
  eval (RBinary _ Equal e1 e2)          = (eval e1) == (eval e2)
  eval (RBinary _ NotEqual e1 e2)       = (eval e1) /= (eval e2)
  eval (RBinary _ Greater e1 e2)        = (eval e1) > (eval e2)
  eval (RBinary _ Less e1 e2)           = (eval e1) < (eval e2)
  eval (RBinary _ GreaterOrEqual e1 e2) = (eval e1) >= (eval e2)
  eval (RBinary _ LessOrEqual e1 e2)    = (eval e1) <= (eval e2)

instance Eval AExpr where
  type Out AExpr = Integer
  eval (Var _  n)                 = 0
  eval (Deref _ e)                = eval e
  eval (IntConst _ i)             = i
  eval (Neg _ e)                  = - eval e
  eval (ABinary _ Add e1 e2)      = eval e1 + eval e2
  eval (ABinary _ Subtract e1 e2) = eval e1 - eval e2
  eval (ABinary _ Multiply e1 e2) = eval e1 * eval e2
  eval (ABinary _ Divide e1 e2)   = quot (eval e1) (eval e2)
  eval (FunctCall _ n args)       = 0

instance Eval Stmt where
  type Out Stmt = (Maybe Integer)
  eval (StmtSeq _ seq)     = Nothing
  eval (VarDeclr _ vars)   = Nothing
  eval (Assign _ e1 e2)    = Nothing
  eval (ExprStmt _ e)      = Nothing
  eval (If _ b s1 s2)      = if eval b then eval s1 else eval s2
  eval (While _ e s)       = Nothing
  eval (DoWhile _ s e)     = Nothing
  eval (Return _ Nothing)  = Nothing
  eval (Return _ (Just e)) = Nothing
  eval (Break _)           = Nothing
  eval (Continue _)        = Nothing
  eval (Skip _)            = Nothing

--instance Eval Declr
--  type Out Declr = Maybe Integer
--  eval (Function _ n args s) = 

