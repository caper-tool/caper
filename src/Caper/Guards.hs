-- TODO: Clean up and properly document
{-# LANGUAGE RankNTypes, MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances, TypeSynonymInstances #-}
{-# LANGUAGE DeriveDataTypeable, FlexibleContexts #-}
{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Caper.Guards where
import Prelude hiding (mapM,sequence,foldl,mapM_,concatMap)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Control.Monad.Exception
import Control.Monad hiding (mapM,sequence)
--import Control.Monad.Trans.Class
--import Control.Monad.Trans.Maybe
import Data.Typeable
import Data.Foldable
import Data.Traversable
--import Data.Maybe
import Data.List (intercalate)
import Control.Monad.State hiding (mapM_,mapM,sequence)
import Debug.Trace              -- TODO: get rid of this
import Control.Lens hiding (op)

import Caper.Parser.AST.Annotation (GuardDeclr(..), TopLevelGuardDeclr(..))
--import qualified Caper.Parser.AST as AST
import Caper.Logger
import Caper.ProverDatatypes
import Caper.Prover
import Caper.Utils.Choice
import Caper.Utils.Mix
--import Caper.Exceptions
-- import Caper.Assertions (generatePermissionExpr, generateValueExpr)


data GuardTypeException =
                GTEMultipleOccurrence String (Maybe GuardDeclr)
                deriving Typeable

instance Show GuardTypeException where
        show (GTEMultipleOccurrence s Nothing) = "Multiple guards named \"" ++ s ++ "\" are declared in a guard type."
        show (GTEMultipleOccurrence s (Just gt)) = "Multiple guards named \"" ++ s ++ "\" are declared in the guard type \"" ++ show gt ++ "\"."

instance Exception GuardTypeException


data GuardParameterType =
                UniqueGPT
                | PermissionGPT
--                | ValueGPT
                deriving (Eq,Ord,Show)

-- INVARIANT : instances of WeakGuardType must be non-empty
type WeakGuardType = Set.Set (Map.Map String GuardParameterType)

validateGuardDeclr :: (Throws GuardTypeException l) => TopLevelGuardDeclr -> EM l ()
validateGuardDeclr ZeroGuardDeclr = return ()
validateGuardDeclr (SomeGuardDeclr gt) = do
                        _ <- vgt Set.empty gt
                        return ()
        where
                vgt s (NamedGD _ n) = checkFresh s n
                vgt s (PermissionGD _ n) = checkFresh s n
--                vgt s (ParametrisedGT n) = checkFresh s n
                vgt s (ProductGD _ gt1 gt2) = do
                                                s1 <- vgt s gt1
                                                vgt s1 gt2
                vgt s (SumGD _ gt1 gt2) = do
                                                s1 <- vgt s gt1
                                                vgt s1 gt2
                checkFresh s n = if Set.member n s then
                                        throw $ GTEMultipleOccurrence n (Just gt)
                                else
                                        return $ Set.insert n s



toWeakGuardType :: GuardDeclr -> WeakGuardType
toWeakGuardType (NamedGD _ n) = Set.singleton $ Map.singleton n UniqueGPT
toWeakGuardType (PermissionGD _ n) = Set.singleton $ Map.singleton n PermissionGPT
--toWeakGuardType (ParametrisedGD n) = Set.singleton $ Map.singleton n ValueGPT
toWeakGuardType (ProductGD _ gt1 gt2) = mixWith Map.union (toWeakGuardType gt1) (toWeakGuardType gt2)
toWeakGuardType (SumGD _ gt1 gt2) = Set.union (toWeakGuardType gt1) (toWeakGuardType gt2)

topLevelToWeakGuardType :: TopLevelGuardDeclr -> WeakGuardType
topLevelToWeakGuardType ZeroGuardDeclr = Set.singleton Map.empty
topLevelToWeakGuardType (SomeGuardDeclr gt) = toWeakGuardType gt


-- toWeakGuardTypeWorker :: WeakGuardType -> GuardType
{-
data GuardAST v =
                EmptyG
                | NamedG String
                | NamedPermissionG String (PermissionExpression v)
                | ParametrisedG String (ValueExpression v)
                | CoParametrisedG String [ValueExpression v]
                | StarG (GuardAST v) (GuardAST v)
                deriving (Functor,Foldable,Traversable)

instance (Show v) => Show (GuardAST v) where
        show EmptyG = "0"
        show (NamedG g) = g
        show (NamedPermissionG g p) = g ++ "[" ++ show p ++ "]"
        show (ParametrisedG g p) = g ++ "(" ++ show p ++ ")"
        show (CoParametrisedG g p) = g ++ "{" ++ show p ++ "}"
        show (StarG a b) = show a ++ " * " ++ show b



data GuardException v =
                GEInconsistentOccurrences String (GuardAST v)
                deriving Typeable

instance Show v => Show (GuardException v) where
        show (GEInconsistentOccurrences s g) = "The guard named \"" ++ s ++ "\" is used inconsistently in the guard expression \"" ++ show g ++ "\"."

instance (Typeable v, Show v) => Exception (GuardException v)
-}

data GuardParameters v = NoGP | PermissionGP (PermissionExpression v)
 --- | Parameters [ValueExpression] | CoParameters [ValueExpression] [ValueExpression]
        deriving (Show,Eq,Ord,Functor,Foldable,Traversable)

newtype Guard v = GD (Map.Map String (GuardParameters v)) deriving (Eq,Ord,Functor,Foldable,Traversable)

emptyGuard :: Guard v
emptyGuard = GD Map.empty

instance Show v => Show (Guard v) where
        show (GD mp) = doshow (Map.toList mp)
                where
                        doshow [] = "0"
                        doshow ll = intercalate " $ " (map showone ll)
                        showone (s, NoGP) = s
                        showone (s, PermissionGP perm) = s ++ "[" ++ show perm ++ "]"

guardLift :: (Map.Map String (GuardParameters t)
               -> Map.Map String (GuardParameters v))
               -> Guard t -> Guard v
guardLift f (GD x) = GD (f x)

instance ExpressionSub GuardParameters PermissionExpression where
        exprSub _ NoGP = NoGP
        exprSub s (PermissionGP pe) = PermissionGP (exprSub s pe)

instance ExpressionSub Guard PermissionExpression where
        exprSub s (GD g) = GD $ Map.map (exprSub s) g

-- This is duplicated code, but to avoid that would need UndecidableInstances
instance ExpressionSub GuardParameters Expr where
        exprSub _ NoGP = NoGP
        exprSub s (PermissionGP pe) = PermissionGP (exprSub s pe)

instance ExpressionSub Guard Expr where
        exprSub s (GD g) = GD $ Map.map (exprSub s) g

-- Code for producing guards will now reside in Caper.Assertions


{-
toGuard :: (Typeable v, Show v, Throws (GuardException v) l) => GuardAST v -> EM l (Guard v)
toGuard gast = tg Map.empty gast
        where
                tg g (EmptyG) = return $ GD g
                tg g (NamedG n) = if n `Map.member` g then throw (GEInconsistentOccurrences n gast) else return . GD $ Map.insert n NoGP g
                tg g (NamedPermissionG n pe) = case Map.lookup n g of
                                        (Nothing) -> return . GD $ Map.insert n (PermissionGP pe) g
                                        (Just (PermissionGP pe0)) -> return . GD $ Map.insert n (PermissionGP (PESum pe0 pe)) g
                                        _ -> throw $ GEInconsistentOccurrences n gast
{--                tg g (ParametrisedG n v) = case Map.lookup n g of
                                        (Nothing) -> return $ Map.insert n (Parameters [v]) g
                                        (Just (Parameters vs)) -> return $ Map.insert n (Parameters (v : vs)) g
                                        (Just (CoParameters vs covs)) -> return $ Map.insert n (CoParameters (v : vs) covs) g
                                        _ -> throw $ GEInconsistentOccurrences n gast
                tg g (CoParametrisedG n vs) = case Map.lookup n g of
                                        (Nothing) -> return $ Map.insert n (CoParameters [] vs) g
                                        (Just (Parameters vs')) -> return $ Map.insert n (CoParameters vs' vs) g
                                        _ -> throw $ GEInconsistentOccurrences n gast --}
                tg g (StarG ge1 ge2) = do
                                                (GD g') <- tg g ge1
                                                tg g' ge2
-}

checkGuardAtType :: Guard v -> WeakGuardType -> Bool
checkGuardAtType (GD g)
  = Set.fold (\ m b -> b || Map.foldWithKey (matchin m) True g) False
        where
                matchin m k p b = b && case Map.lookup k m of
                                Nothing -> False
                                (Just x) -> matchup p x
                matchup NoGP UniqueGPT = True
                matchup (PermissionGP _) PermissionGPT = True
--                matchup (Parameters _) ValueGPT = True
--                matchup (CoParameters _ _) ValueGPT = True
                matchup _ _ = False

gtToG :: GuardParameterType -> GuardParameters v
gtToG UniqueGPT = NoGP
gtToG PermissionGPT = PermissionGP PEFull
--gtToG ValueGPT = CoParameters [] []

fullGuard :: WeakGuardType -> Guard v
fullGuard gt = GD $ Map.map gtToG (Set.findMin gt)

fullGuards :: WeakGuardType -> [Guard v]
fullGuards = Prelude.map (GD . Map.map gtToG) . Set.toList


guardJoin :: Guard v -> Guard v -> Guard v
guardJoin (GD g1) (GD g2) = GD $ Map.union g1 g2


-- Merge two guards, generating assumptions in the process
mergeGuards :: (MonadState s m, AssumptionLenses s) =>
                Guard VariableID -> Guard VariableID -> m (Guard VariableID)
mergeGuards (GD g1) (GD g2) = liftM GD $ sequence (Map.unionWith unionop (fmap return g1) (fmap return g2))
        where
                unionop p1 p2 = do
                                v1 <- p1
                                v2 <- p2
                                case (v1, v2) of
                                        (PermissionGP perm1, PermissionGP perm2) -> do
                                                -- Assume both contributions are non-zero
                                                -- WARNING: this assumption is subtle
                                                assumeFalse $ PAEq perm1 PEZero
                                                assumeFalse $ PAEq perm2 PEZero
                                                assumeTrue $ PADis perm1 perm2
                                                return $ PermissionGP $ PESum perm1 perm2
                                        _ -> do
                                                assumeContradiction
                                                -- Since we've assumed false, it shouldn't
                                                -- matter what we return here...
                                                return v1


guardEquivalence :: GuardDeclr -> Guard v1 -> Guard v2 -> (Guard v3, Guard v4)
-- Given a GuardDeclr and a pair of guards, find a pair of guards that
-- could be used to rewrite the first to entail the second.
-- This assumes the guards conform to the guard type.
guardEquivalence (ProductGD _ gta1 gta2) gd1 gd2 = (guardJoin gd3a gd3b, guardJoin gd4a gd4b)
        where
                (gd3a, gd4a) = guardEquivalence gta1 gd1 gd2
                (gd3b, gd4b) = guardEquivalence gta2 gd1 gd2
guardEquivalence (SumGD _ gta1 gta2) gd1 gd2 =
                case (ma gta1 gd1, ma gta2 gd1, ma gta1 gd2, ma gta2 gd2) of
                                        (True, _, True, _) -> guardEquivalence gta1 gd1 gd2
                                        (True, _, _, True) -> (fgf gta1 gd1, fgf gta2 gd2)
                                        (_, True, _, True) -> guardEquivalence gta2 gd1 gd2
                                        (_, True, True, _) -> (fgf gta2 gd1, fgf gta1 gd2)
                                        _ -> (GD Map.empty, GD Map.empty)
                where
                        ma :: GuardDeclr -> Guard v -> Bool
                        ma (NamedGD _ n) (GD g) = Map.member n g
                        ma (PermissionGD _ n) (GD g) = Map.member n g
                        ma (ProductGD _ t1 t2) g = ma t1 g || ma t2 g
                        ma (SumGD _ t1 t2) g = ma t1 g || ma t2 g
                        fgf :: GuardDeclr -> Guard v -> Guard w
                        fgf (NamedGD _ n) _ = GD $ Map.singleton n NoGP
                        fgf (PermissionGD _ n) _ = GD $ Map.singleton n (PermissionGP PEFull)
                        fgf (ProductGD _ gt1 gt2) g = guardJoin (fgf gt1 g) (fgf gt2 g)
                        fgf (SumGD _ gt1 gt2) g = if ma gt2 g then fgf gt2 g else fgf gt1 g

guardEquivalence _ _ _ = (GD Map.empty, GD Map.empty)


sameGuardParametersType :: GuardParameters v -> GuardParameters w -> Maybe (GuardParameters v)
sameGuardParametersType NoGP NoGP = Nothing
sameGuardParametersType (PermissionGP _) (PermissionGP _) = Nothing
sameGuardParametersType a _ = Just a

subtractPE :: (MonadPlus m, MonadState s m, AssertionLenses s, MonadLogger m) =>
        PermissionExpression VariableID -> PermissionExpression VariableID ->
                m (Maybe (PermissionExpression VariableID))
subtractPE l PEFull = do
                        assertTrue $ PAEq l PEFull
                        return Nothing
subtractPE _ PEZero = mzero     -- Having a permission guard at all should imply that it's non-zero, therefore this path can simply fail
{--subtractPE l ex@(PEVar (EVExistential _ s)) = trace ("binding: " ++ s ++ " === " ++ show l) (do
                        bindEvar s l -- TODO: frame some permission off?
                        return Nothing) `mplus`
                (do
                        ev <- freshEvar
                        let eve = (PEVar $ EVExistential () ev)
                        trace ("binding: " ++ s ++ " + " ++ ev ++ " === " ++ show l) $ addConstraint $ LNeg $ PAEq ex PEZero
                        addConstraint $ LNeg $ PAEq eve PEZero
                        addConstraint $ LPos $ PAEq (fmap EVNormal l) (PESum ex eve)
                        return (Just eve))
--}
subtractPE l s = (do -- TODO: frame some permission
                assertTrue $ PAEq l s
                return Nothing) `mplus`
        trace "Trying framing" (do
                ev <- newEvar "perm"
                let eve = PEVar ev
                assertFalse $ PAEq s PEZero
                assertFalse $ PAEq eve PEZero
                assertTrue $ PAEq l (PESum s eve)
                return (Just eve))

-- |Given a guard parameter we have, take away a given guard parameter.
-- If things are of the wrong type, backtrack rather than erroring, because
-- we might just have picked the wrong region.
subtractGP :: (MonadPlus m, MonadState s m, AssertionLenses s, MonadLogger m) =>
        GuardParameters VariableID -> GuardParameters VariableID ->
                m (Maybe (GuardParameters VariableID))
subtractGP NoGP NoGP = return Nothing
subtractGP (PermissionGP p1) (PermissionGP p2) =
                liftM (liftM PermissionGP) $ subtractPE p1 p2
subtractGP _ _ = mzero

guardPrimitiveEntailmentM :: (MonadPlus m, MonadState s m, AssertionLenses s,
        MonadLogger m) =>
                Guard VariableID -> Guard VariableID -> m (Guard VariableID)
guardPrimitiveEntailmentM (GD g1) (GD g2) = if Map.null $ Map.differenceWith sameGuardParametersType g2 g1 then liftM GD doGPEM else mzero
        where
                rest = Map.difference g1 g2
                doGPEM = do
                        let k = Map.intersectionWith (,) g1 g2
                        r <- mapM subtrct k
                        return $ Map.union (Map.mapMaybe id r) rest
                subtrct :: (MonadPlus m, MonadState s m, AssertionLenses s,
                        MonadLogger m) =>
                        (GuardParameters VariableID, GuardParameters VariableID) -> m (Maybe (GuardParameters VariableID))
                subtrct (NoGP, NoGP) = return Nothing
                subtrct (PermissionGP pe1, PermissionGP pe2) = liftM (fmap PermissionGP) $ subtractPE pe1 pe2
                subtrct _ = mzero -- Should be impossible


guardEntailment :: (MonadPlus m, MonadState s m, AssertionLenses s,
        MonadLogger m) =>
                GuardDeclr -> Guard VariableID -> Guard VariableID ->
                        m (Guard VariableID)
guardEntailment gt g1 g2 = guardPrimitiveEntailmentM g1 g2 `mplus`
                        do
                                let (gel, ger) = guardEquivalence gt g1 g2
                                frame1 <- guardPrimitiveEntailmentM g1 gel
                                guardPrimitiveEntailmentM (guardJoin frame1 ger) g2

-- |Try to extract a single guard resource, where we don't know the guard type.
-- Consequently, no rewriting of guards is possible.
consumeGuardNoType :: (MonadPlus m, MonadState s m, AssertionLenses s,
        MonadLogger m) =>
                String -> GuardParameters VariableID ->
                Guard VariableID -> m (Guard VariableID)
consumeGuardNoType gname gpara (GD g) = do
                        gp <- liftMaybe $ g ^. at gname
                        gp' <- subtractGP gp gpara
                        return $ GD $ at gname .~ gp' $ g

consumeGuard' :: (MonadPlus m, MonadState s m, AssertionLenses s,
        MonadLogger m) =>
                GuardDeclr ->
                String -> GuardParameters VariableID ->
                Guard VariableID -> m (Guard VariableID)
consumeGuard' gt gname gpara g = consumeGuardNoType gname gpara g `mplus`
                do
                        let (gel, ger) = guardEquivalence gt g
                                (GD $ Map.insert gname gpara Map.empty)
                        frame1 <- guardPrimitiveEntailmentM g gel
                        consumeGuardNoType gname gpara (guardJoin frame1 ger)

consumeGuard :: (MonadPlus m, MonadState s m, AssertionLenses s,
        MonadLogger m) =>
                TopLevelGuardDeclr ->
                String -> GuardParameters VariableID ->
                Guard VariableID -> m (Guard VariableID)
consumeGuard ZeroGuardDeclr = \_ _ _ -> mzero -- Something has gone wrong...
consumeGuard (SomeGuardDeclr gt) = consumeGuard' gt

{--


guardPrimitiveEntailment :: (MonadIO m, Monad m) => p -> Guard VariableID -> Guard EVariable -> ProverT (MaybeT m) (Guard EVariable, EvarSubstitution)
-- Checks if first guard entails second without rewrites
-- Returns the frame and substitution if so, Nothing otherwise
guardPrimitiveEntailment prover g1@(GD g1a) g2@(GD g2a) = if Map.null $ g2a `Map.difference` g1a then dogpe else fail "Non sequitur"
        where
                dogpe = do
                        (frame, subs) <- mapProver firstChoiceT $ checkWith prover $ guardPrimitiveEntailmentM g1 g2
                        return (frame, subs)
                        --return (exprSub subs frame, subs)
--

eGuardSubs :: Guard EVariable -> EvarSubstitution -> Guard VariableID
eGuardSubs g subs = exprSub (fromJust . subs) g

guardGeneralEntailment :: (MonadIO m, Monad m, PermissionsProver p) => p -> GuardDeclr -> Guard VariableID -> Guard EVariable -> ProverT (MaybeT m) (Guard EVariable, EvarSubstitution)
guardGeneralEntailment p gt g1 g2 = guardPrimitiveEntailment p g1 g2 `mplus`
                (do
                        let (gel, ger) = guardEquivalence gt g1 g2
                        (frame0, s0) <- guardPrimitiveEntailment p g1 gel
                        guardPrimitiveEntailment p (guardJoin (eGuardSubs frame0 s0) ger) g2)

--}
