{-# LANGUAGE FlexibleContexts #-}
module Caper.Assertions where

import Data.Foldable
import Control.Monad.State
import Control.Monad.Reader
--import Control.Monad.Exception
import Control.Lens
import qualified Data.Map as Map

import Caper.Utils.SimilarStrings
import Caper.Exceptions
import Caper.ProverDatatypes
import Caper.Prover
import Caper.Parser.AST
import Caper.Parser.AST.SourcePos
import Caper.SymbolicState (SymbStateLenses, PredicateName(..))
import qualified Caper.SymbolicState as SS
import Caper.Regions (RegionLenses)
import qualified Caper.Regions as R
import Caper.RegionTypes
import qualified Caper.Guards as G

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



-- |Given a syntactic pure assertion, produce it by adding it as an assumption.
producePure :: (MonadState s m, AssumptionLenses s, MonadRaise m) =>
                PureAssrt -> m ()
producePure = producePure' False
        where
                producePure' b (NotBAssrt _ pa) = producePure' (not $! b) pa
                producePure' b (ConstBAssrt _ b') = when (b == b') assumeContradiction
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
generatePermissionExpr genvar (ConstPermExpr _ FullPerm) = return PEFull
generatePermissionExpr genvar (ConstPermExpr _ EmptyPerm) = return PEZero
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

generateCellPred :: (Monad m, MonadRaise m) =>
        (VarExpr -> m VariableID)
        -> CellAssrt
        -> m SS.Predicate
generateCellPred genvar (Cell sp e1 e2) = do
                ve1 <- generateValueExpr genvar e1
                ve2 <- generateValueExpr genvar e2
                return (PCell, [ValueExpr ve1, ValueExpr ve2])
generateCellPred genvar (CellBlock sp e1 e2) = do
                ve1 <- generateValueExpr genvar e1
                ve2 <- generateValueExpr genvar e2
                return (PCells, [ValueExpr ve1, ValueExpr ve2])

produceCell :: (MonadState s m, AssumptionLenses s, SymbStateLenses s, MonadRaise m) =>
        CellAssrt -> m ()
produceCell p = generateCellPred produceVariable p >>= SS.producePredicate

consumeCell :: (MonadPlus m, MonadState s m, AssertionLenses s,
        SymbStateLenses s, MonadRaise m) =>
        CellAssrt -> m ()
-- Note: it shouldn't be necessary to check the number and type of arguments
-- after the call to generateCellPred.
consumeCell p = generateCellPred consumeVariable p >>= SS.consumePred 

-- |Check that the list of parameters for a region is of the right length and 
-- that each parameter is of the appropriate type.
checkRegionParams :: (MonadState s m, AssumptionLenses s,
                MonadReader r m, RTCGetter r,
                MonadRaise m) =>
        RTId -> [(Expr VariableID, AnyExpr)] -> m ()
checkRegionParams rtid params = do
                        rt <- lookupRType rtid
                        let types = map snd $ rtParameters rt
                        if length types == length params then
                                checkParams (2 :: Int) params types
                            else
                                raise $ ArgumentCountMismatch (2 + length types) (2 + length params)
        where
                checkParams n ((e, p) : ps) (t : ts) = do
                        addContext (DescriptiveContext (sourcePos p) $
                                        "In argument " ++ show n) $
                                checkExpressionAtTypeE e t
                        checkParams (n+1) ps ts
                checkParams _ _ _ = return () 

-- |Produce a region assertion.
produceRegion :: (MonadState s m, AssumptionLenses s, RegionLenses s,
                MonadReader r m, RTCGetter r,
                MonadRaise m) =>
        Bool -- ^Should the region be treated as dirty (unstable)
        -> RegionAssrt -> m ()
produceRegion dirty (Region sp rtn ridv lrps rse) = addContext
        (DescriptiveContext sp $ "In a region assertion of type '" ++ rtn ++ "'") $
        do
                rtid0 <- view $ lookupRTName rtn
                case rtid0 of
                        Nothing -> do
                                rtnames <- view regionTypeNames
                                raise $ UndeclaredRegionType rtn (similarStrings rtn rtnames)
                        (Just rtid) -> do
                                let rid = VIDNamed ridv
                                addContext (StringContext $ "The region identifier '" ++ ridv ++ "'") $
                                        bindVarAs rid VTRegionID
                                params <- mapM produceAnyExpr lrps
                                checkRegionParams rtid (zip params lrps)
                                state <- produceValueExpr rse
                                R.produceMergeRegion rid $ R.Region dirty (Just $ R.RegionInstance rtid params) (Just state) G.emptyGuard

-- |Produce a guard assertion.
-- If the guards are not compatible with a guard type for the region,
-- this will result in an assumption of inconsistency.  However, if the
-- guards are syntactically incompatible, an exception is raised instead.
produceGuards :: (MonadState s m, AssumptionLenses s, RegionLenses s,
                MonadReader r m, RTCGetter r,
                MonadRaise m) =>
        Guards -> m ()
produceGuards gg@(Guards _ rid gds) = contextualise gg $
                do
                        let rrid = VIDNamed rid
                        bindVarAs rrid VTRegionID
                        guards <- liftM G.GD $ foldlM mkGuards Map.empty gds
                        R.produceMergeRegion rrid $
                                R.Region False Nothing Nothing guards
        where
                mkGuards g gd@(NamedGuard sp nm) = contextualise gd $
                        if nm `Map.member` g then
                                raise $ IncompatibleGuardOccurrences nm
                        else
                                return $ Map.insert nm G.NoGP g
                mkGuards g gd@(PermGuard sp nm pe) = contextualise gd $ do
                        ppe <- producePermissionExpr pe
                        case Map.lookup nm g of
                                Nothing -> return $
                                        Map.insert nm (G.PermissionGP ppe) g
                                (Just (G.PermissionGP pe0)) -> return $
                                        Map.insert nm
                                                (G.PermissionGP (PESum pe0 ppe))
                                                g
                                _ -> raise $ IncompatibleGuardOccurrences nm  
                mkGuards g gd@(ParamGuard sp nm es) = contextualise gd $
                        raise $ SyntaxNotImplemented "parametrised guards"

producePredicate :: (MonadState s m, AssumptionLenses s,
                MonadRaise m) =>
        Predicate -> m ()
producePredicate pa = contextualise pa $
        raise $ SyntaxNotImplemented "predicates"
        
produceSpatial :: (MonadState s m, AssumptionLenses s, RegionLenses s,
                SymbStateLenses s,
                MonadReader r m, RTCGetter r,
                MonadRaise m) =>
        Bool ->
        SpatialAssrt -> m ()
produceSpatial dirty (SARegion a) = produceRegion dirty a
produceSpatial _ (SAPredicate a) = producePredicate a
produceSpatial _ (SACell a) = produceCell a
produceSpatial _ (SAGuards a) = produceGuards a

produceAssrt ::  (MonadState s m, AssumptionLenses s, RegionLenses s,
                SymbStateLenses s,
                MonadReader r m, RTCGetter r,
                MonadRaise m) =>
        Bool -> 
        Assrt -> m ()
produceAssrt _ (AssrtPure sp a) = producePure a
produceAssrt dirty (AssrtSpatial sp a) = produceSpatial dirty a
produceAssrt dirty (AssrtConj sp a1 a2) = produceAssrt dirty a1 >>
                                        produceAssrt dirty a2
produceAssrt _ (AssrtITE sp c a1 a2) = addContext (SourcePosContext sp) $
        raise $ SyntaxNotImplemented "... ? ... : ... (conditional assertions)"