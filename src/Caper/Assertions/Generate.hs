{-# LANGUAGE FlexibleContexts, ScopedTypeVariables, MultiParamTypeClasses #-}
module Caper.Assertions.Generate where

import Control.Monad.State hiding (state)
import qualified Data.Map as Map

import Caper.Utils.AliasingMap ()
import Caper.Exceptions
import Caper.ProverDatatypes
import Caper.Parser.AST
import Caper.Predicates as P
import qualified Caper.Guards as G

{-
        At some point, this whole module should probably be rewritten.
        In particular, some consideration of where variables are bound to
        types would be good.

        At present types are NOT bound by
                {produce,consume}{Value,Permission}Expr.
        This means that one should be careful to bind them correctly at point
        of use.
-}

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
valueBinOp ValDivide = raise $ SyntaxNotImplemented "/ (division in assertions)"

-- |Interpret a syntactic permission relation.
permissionRel :: PermBinRel -> PermissionExpression v -> PermissionExpression v -> FOF PermissionAtomic v
permissionRel (PermEquality EqualRel) e1 e2 = FOFAtom $ PAEq e1 e2
permissionRel (PermEquality NotEqualRel) e1 e2 = FOFNot $ FOFAtom $ PAEq e1 e2
permissionRel Compatible e1 e2 = FOFAtom $ PADis e1 e2

-- |Interpret a syntactic binary permission operator.
permissionBinOp :: PermBinOp -> PermissionExpression v -> PermissionExpression v -> PermissionExpression v
permissionBinOp Composition = PESum

generateValueExpr :: (Monad m, MonadRaise m) =>
        (VarExpr -> m v)       -- ^Variable handler
        -> ValExpr                      -- ^Syntactic value expression
        -> m (ValueExpression v)
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


generatePermissionExpr :: (Monad m) =>
        (VarExpr -> m v)       -- ^Variable handler
        -> PermExpr                     -- ^Syntactic permission expression
        -> m (PermissionExpression v)
generatePermissionExpr genvar (VarPermExpr _ ve) = liftM var $ genvar ve
generatePermissionExpr genvar (ConstPermExpr _ FullPerm) = return PEFull
generatePermissionExpr genvar (ConstPermExpr _ EmptyPerm) = return PEZero
generatePermissionExpr genvar (UnaryPermExpr _ Complement pe) = liftM PECompl $ generatePermissionExpr genvar pe
generatePermissionExpr genvar (BinaryPermExpr _ bo pe1 pe2) = do
                        let op = permissionBinOp bo
                        ppe1 <- generatePermissionExpr genvar pe1
                        ppe2 <- generatePermissionExpr genvar pe2
                        return $ op ppe1 ppe2

generateAnyExpr :: (Monad m, MonadRaise m) =>
        (VarExpr -> m VariableID)       -- ^Variable handler
        -> AnyExpr                      -- ^Syntactic expression
        -> m (Expr VariableID)
generateAnyExpr genvar (AnyVar e) = liftM VariableExpr $ genvar e
generateAnyExpr genvar (AnyVal e) = liftM ValueExpr $ generateValueExpr genvar e
generateAnyExpr genvar (AnyPerm e) = liftM PermissionExpr $ generatePermissionExpr genvar e

generateCellPred :: (Monad m, MonadRaise m) =>
        (VarExpr -> m VariableID)
        -> CellAssrt
        -> m P.Predicate
generateCellPred genvar (Cell sp e1 e2) = do
                ve1 <- generateValueExpr genvar e1
                ve2 <- generateValueExpr genvar e2
                return (PCell, [ValueExpr ve1, ValueExpr ve2])
generateCellPred genvar (CellBlock sp e1 e2) = do
                ve1 <- generateValueExpr genvar e1
                ve2 <- generateValueExpr genvar e2
                return (PCells, [ValueExpr ve1, ValueExpr ve2])

-- |Convert a list of AST guards to the map-based internal representation of
-- guards.  For practical purposes, this works like producing the guard.
--
-- TODO: it might be nice if produceGuards and consumeGuards went via this.
generateGuard :: forall m v. (MonadRaise m, Monad m, Refreshable v, StringVariable v, Eq v) =>
            (VarExpr -> m v) 
            -- ^ Variable handler
            -> (Condition v -> m ())
            -- ^ Handler for conditions
            -> [Guard]
            -- ^ Guard AST 
            -> m (G.Guard v)
generateGuard handler condh = liftM G.GD . foldM tg' Map.empty
    where
        tg' g grd = contextualise grd $ tg g grd
        tg :: Map.Map String (G.GuardParameters v) -> Guard -> m (Map.Map String (G.GuardParameters v))
        tg g (NamedGuard _ gname) = if gname `Map.member` g then
                    raise (IncompatibleGuardOccurrences gname)
                else
                    return $ Map.insert gname G.NoGP g
        tg g (PermGuard _ gname pe) = case Map.lookup gname g of
                        Nothing -> do
                            pexp <- gpe pe
                            return $ Map.insert gname (G.PermissionGP pexp) g
                        (Just (G.PermissionGP pe0)) -> do
                            pexp <- gpe pe
                            condh $ toCondition $ PADis pe0 pexp
                            return $ Map.insert gname
                                        (G.PermissionGP (PESum pe0 pexp)) g
                        _ -> raise $ IncompatibleGuardOccurrences gname
        tg g (ParamGuard _ gname [e]) = do
                    v <- generateValueExpr handler e
                    let s = SetSingleton v
                    case Map.lookup gname g of
                        Nothing -> return $ Map.insert gname (G.ParameterGP s) g
                        Just (G.ParameterGP s0) -> do
                            condh $ toCondition $ SubsetEq (setIntersection s0 s) emptySet
                            return $ Map.insert gname (G.ParameterGP (setUnion s0 s)) g
                        _ -> raise $ IncompatibleGuardOccurrences gname                            
        tg g (ParamGuard _ gname _) = raise $ SyntaxNotImplemented "guards with multiple parameters"
        tg g (ParamSetGuard{}) = raise $ SyntaxNotImplemented "parametrised guards"
        gpe :: PermExpr -> m (PermissionExpression v)
        gpe pe = do
            pexp <- generatePermissionExpr handler pe
            condh $ negativeCondition $ PAEq pexp PEZero
            return pexp



guardToNameParam :: (Monad m, MonadRaise m) =>
        (VarExpr -> m VariableID) ->
        Guard -> m (String, G.GuardParameters VariableID)
guardToNameParam _ (NamedGuard _ nm) = return (nm, G.NoGP)
guardToNameParam genv gd@(PermGuard _ nm pe) = contextualise gd $ do
                                ppe <- generatePermissionExpr genv pe
                                return (nm, G.PermissionGP ppe)
guardToNameParam genv gd@(ParamGuard {}) = contextualise gd $
                        raise $ SyntaxNotImplemented "parametrised guards"

generatePure :: (MonadRaise m, Monad m) =>
            (VarExpr -> m v) -> PureAssrt -> m (Condition v)
generatePure handler assn = contextualise assn $ generatePure' False assn
        where
            mkCond b = if b then negativeCondition else toCondition 
            generatePure' b (NotBAssrt _ pa) = generatePure' (not $! b) pa
            generatePure' b (ConstBAssrt _ b') = return (if b == b' then condFalse else condTrue)
            generatePure' b (BinaryVarAssrt sp ebo vl vr) = do -- The only two cases are equality and disequality
                            vvl <- handler vl
                            vvr <- handler vr
                            return $ mkCond (b == (ebo == EqualRel)) (EqualityCondition vvl vvr)
            generatePure' b (BinaryValAssrt sp bo vel ver) = do
                            vvel <- generateValueExpr handler vel
                            vver <- generateValueExpr handler ver
                            return $ mkCond b $ valueRel bo vvel vver
            generatePure' b (BinaryPermAssrt sp brel pel per) = do
                            ppel <- generatePermissionExpr handler pel
                            pper <- generatePermissionExpr handler per
                            return $ mkCond b $ permissionRel brel ppel pper