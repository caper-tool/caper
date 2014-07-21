{-# LANGUAGE FlexibleContexts #-}
module Assertions where

import Control.Monad.State
import Control.Monad.Reader
--import Control.Monad.Exception
import Control.Lens

import Utils.SimilarStrings
import Exceptions
import ProverDatatypes
import Prover
import Parser.AST
import SymbolicState (SymbStateLenses, PredicateName(..))
import qualified SymbolicState as SS
import Regions (RegionLenses)
import qualified Regions as R
import RegionTypes

-- TODO: Check for sure that I've got these right(!)
-- |Interpret a syntactic value relation.
valueRel :: ValBinRel -> ValueExpression v -> ValueExpression v -> FOF ValueAtomic v
valueRel (ValEquality EqualRel) e1 e2 = FOFAtom $ VAEq e1 e2
valueRel (ValEquality NotEqualRel) e1 e2 = FOFNot $ FOFAtom $ VAEq e1 e2
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

-- |Interpret a syntactic permission relation.
permissionRel :: PermBinRel -> PermissionExpression v -> PermissionExpression v -> FOF PermissionAtomic v
permissionRel (PermEquality EqualRel) e1 e2 = FOFAtom $ PAEq e1 e2
permissionRel (PermEquality NotEqualRel) e1 e2 = FOFNot $ FOFAtom $ PAEq e1 e2
permissionRel Compatible e1 e2 = FOFAtom $ PADis e1 e2

-- |Interpret a syntactic binary permission operator.
permissionBinOp :: PermBinOp -> PermissionExpression v -> PermissionExpression v -> PermissionExpression v
permissionBinOp Composition e1 e2 = PESum e1 e2



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
                                addSPContext sp $ (if b /= (ebo == EqualRel) then
                                        assumeTrueE else assumeFalseE)
                                        (EqualityCondition vvl vvr)
                producePure' b (BinaryValAssrt sp bo vel ver) = do
                                vvel <- produceValueExpr vel
                                vver <- produceValueExpr ver
                                addSPContext sp $ (if b then assumeFalseE else assumeTrueE) $
                                        valueRel bo vvel vver
                producePure' b (BinaryPermAssrt sp brel pel per) = do
                                let rel = permissionRel brel
                                ppel <- producePermissionExpr pel
                                pper <- producePermissionExpr per
                                (if b then assumeFalseE else assumeTrueE)
                                        $ rel ppel pper

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

consumeVariable :: (MonadState s m, AssertionLenses s) =>
                VarExpr -> m VariableID
consumeVariable (Variable _ vname) = do
                        let v = VIDNamed vname
                        b <- isBound v
                        if b then return v else declareEvar v >> return v
consumeVariable (WildCard _) =
                        newEvar "wildcard"

generateValueExpr :: (Monad m, MonadRaise m) =>
        (VarExpr -> m VariableID)       -- ^Variable handler
        -> ValExpr                      -- ^Syntactic value expression
        -> m (ValueExpression VariableID)
-- Note: it might give a better error report if we try to bind the variable
-- type here (although this would be redundant).  Likewise in producePermissionExpr.
generateValueExpr genvar (VarValExpr _ ve) = liftM var $ genvar ve
generateValueExpr genvar (ConstValExpr _ n) = return $ VEConst n
generateValueExpr genvar (UnaryValExpr _ ValNegation ve) =
                liftM (VEMinus (VEConst 0)) $ generateValueExpr genvar ve
generateValueExpr genvar (BinaryValExpr sp bo ve1 ve2) = do
                        op <- addSPContext sp $ valueBinOp bo
                        vve1 <- generateValueExpr genvar ve1
                        vve2 <- generateValueExpr genvar ve2
                        return $ op vve1 vve2
generateValueExpr genvar (SetValExpr sp _) = addSPContext sp $ raise $ SyntaxNotImplemented "{ ... } (set of values notation in assertions)"

produceValueExpr :: (MonadState s m, AssumptionLenses s, MonadRaise m) =>
        ValExpr -> m (ValueExpression VariableID)
produceValueExpr = generateValueExpr produceVariable

generatePermissionExpr :: (Monad m) =>
        (VarExpr -> m VariableID)       -- ^Variable handler
        -> PermExpr                     -- ^Syntactic permission expression
        -> m (PermissionExpression VariableID)
generatePermissionExpr genvar (VarPermExpr _ ve) = liftM var $ genvar ve
generatePermissionExpr genvar (ConstPermExpr _ FullPerm) = return $ PEFull
generatePermissionExpr genvar (ConstPermExpr _ EmptyPerm) = return $ PEZero
generatePermissionExpr genvar (UnaryPermExpr _ Complement pe) = liftM PECompl $ generatePermissionExpr genvar pe
generatePermissionExpr genvar (BinaryPermExpr _ bo pe1 pe2) = do
                        let op = permissionBinOp bo
                        ppe1 <- generatePermissionExpr genvar pe1
                        ppe2 <- generatePermissionExpr genvar pe2
                        return $ op ppe1 ppe2

producePermissionExpr :: (MonadState s m, AssumptionLenses s) =>
        PermExpr -> m (PermissionExpression VariableID)
producePermissionExpr = generatePermissionExpr produceVariable

generateAnyExpr :: (Monad m, MonadRaise m) =>
        (VarExpr -> m VariableID)       -- ^Variable handler
        -> AnyExpr                      -- ^Syntactic expression
        -> m (Expr VariableID)
generateAnyExpr genvar (AnyVar e) = liftM VariableExpr $ genvar e
generateAnyExpr genvar (AnyVal e) = liftM ValueExpr $ generateValueExpr genvar e
generateAnyExpr genvar (AnyPerm e) = liftM PermissionExpr $ generatePermissionExpr genvar e

produceAnyExpr :: (MonadState s m, AssumptionLenses s, MonadRaise m) =>
        AnyExpr -> m (Expr VariableID)
produceAnyExpr = generateAnyExpr produceVariable

produceCell :: (MonadState s m, AssumptionLenses s, SymbStateLenses s, MonadRaise m) =>
        CellAssrt -> m ()
produceCell p = mkPred p >>= SS.producePredicate
        where
                mkPred (Cell sp e1 e2) = do
                                ve1 <- produceValueExpr e1
                                ve2 <- produceValueExpr e2
                                return $ (PCell, [ValueExpr ve1, ValueExpr ve2])
                mkPred (CellBlock sp e1 e2) = do
                                ve1 <- produceValueExpr e1
                                ve2 <- produceValueExpr e2
                                return $ (PCells, [ValueExpr ve1, ValueExpr ve2])

produceRegion :: (MonadState s m, AssumptionLenses s, RegionLenses s,
                MonadReader r m, RTCGetter r,
                MonadRaise m) =>
        Bool -> -- ^Should the region be treated as dirty (unstable)
        RegionAssrt -> m ()
produceRegion dirty (Region sp rtn ridv lrps rse) = do
                rtid0 <- view $ lookupRTName rtn
                case rtid0 of
                        Nothing -> do
                                rtnames <- view regionTypeNames
                                raise $ UndeclaredRegionType rtn (similarStrings rtn rtnames)
                        (Just rtid) -> do
                                let id = VIDNamed ridv
                                params <- mapM produceAnyExpr lrps
                                state <- produceValueExpr rse
                                undefined -- R.Region dirty (Just $ R.RegionInstance rtid params) state 
