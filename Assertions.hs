{-# LANGUAGE FlexibleContexts #-}
module Assertions where

import Control.Monad.State
--import Control.Monad.Exception

import Exceptions
import ProverDatatypes
import Prover
import Parser.AST


-- TODO: Check for sure that I've got these right(!)
-- |Interpret a syntactic value relation.
valueRel :: ValRBinOp -> ValueExpression v -> ValueExpression v -> FOF ValueAtomic v
valueRel (ValEquality ValEqual) e1 e2 = FOFAtom $ VAEq e1 e2
valueRel (ValEquality ValNotEqual) e1 e2 = FOFNot $ FOFAtom $ VAEq e1 e2
valueRel ValGreater e1 e2 = FOFAtom $ VALt e2 e1
valueRel ValGreaterOrEqual e1 e2 = FOFNot $ FOFAtom $ VALt e1 e2
valueRel ValLess e1 e2 = FOFAtom $ VALt e1 e2
valueRel ValLessOrEqual e1 e2 = FOFNot $ FOFAtom $ VALt e2 e1

-- |Interpret a syntactic binary value operator.
-- Division is not currently supported, and so raises an exception.
valueBinOp :: (Monad m, MonadRaise m) => ValBinOp -> m (ValueExpression v -> ValueExpression v -> ValueExpression v)
valueBinOp ValAdd = return VEPlus
valueBinOp ValSubtract = return VEMinus
valueBinOp ValMultiply = return VETimes
valueBinOp ValDivide = raise $ SyntaxNotImplemented $ "/ (division in assertions)"


-- |Given a syntactic pure assertion, produce it by adding it as an assumption.
producePure :: (MonadState s m, AssumptionLenses s, MonadRaise m) =>
                PureAssrt -> m ()
producePure = producePure' False
        where
                producePure' b (NotBAssrt _ pa) = producePure' (not $! b) pa
                producePure' b (ConstBAssrt _ b') = if b /= b' then
                                                return ()
                                        else
                                                assumeContradiction
                producePure' b (BinaryVarAssrt sp ebo vl vr) = do
                                vvl <- produceVariable vl
                                vvr <- produceVariable vr
                                addSPContext sp $ (if b /= (ebo == ValEqual) then
                                        assumeTrueE else assumeFalseE)
                                        (EqualityCondition vvl vvr)
                producePure' b (BinaryValAssrt sp bo vel ver) = do
                                vvel <- produceValueExpr vel
                                vver <- produceValueExpr ver
                                addSPContext sp $ (if b then assumeFalseE else assumeTrueE) $
                                        valueRel bo vvel vver

-- |Produce a variable.  Named variables are converted to 'VIDNamed'
-- instances, and declared in the assumptions.  Anonymous (wildcard)
-- variables are translated to fresh identifiers.
produceVariable :: (MonadState s m, AssumptionLenses s) =>
                VarExpr -> m VariableID
produceVariable (Variable _ vname) = do
                        let v = VIDNamed vname
                        declareVar v
                        return v
produceVariable (WildCard _) =
                        newAvar "wildcard"

produceValueExpr :: (MonadState s m, AssumptionLenses s, MonadRaise m) =>
                ValExpr -> m (ValueExpression VariableID)
produceValueExpr (VarValExpr _ ve) = liftM var $ produceVariable ve
produceValueExpr (ConstValExpr _ n) = return $ VEConst n
produceValueExpr (UnaryValExpr _ ValNegation ve) =
                liftM (VEMinus (VEConst 0)) $ produceValueExpr ve
produceValueExpr (BinaryValExpr sp bo ve1 ve2) = do
                        op <- addSPContext sp $ valueBinOp bo
                        vve1 <- produceValueExpr ve1
                        vve2 <- produceValueExpr ve2
                        return $ op vve1 vve2
produceValueExpr (SetValExpr sp _) = addSPContext sp $ raise $ SyntaxNotImplemented "{ ... } (set of values notation in assertions)"
