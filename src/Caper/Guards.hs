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
import Control.Monad hiding (mapM,sequence)
import Data.Foldable
import Data.Traversable
import Data.List (intercalate)
import Control.Monad.State hiding (mapM_,mapM,sequence)
import Debug.Trace              -- TODO: get rid of this
import Control.Lens hiding (op)

import Caper.Parser.AST.Annotation (GuardDeclr(..), TopLevelGuardDeclr(..))
import Caper.Logger
import Caper.ProverDatatypes
import Caper.Prover
import Caper.Utils.NondetClasses
import Caper.Utils.Mix
import Caper.Exceptions



data GuardParameterType =
                UniqueGPT
                | PermissionGPT
--                | ValueGPT
                deriving (Eq,Ord,Show)

-- INVARIANT : instances of WeakGuardType must be non-empty
type WeakGuardType = Set.Set (Map.Map String GuardParameterType)

validateGuardDeclr :: (MonadRaise m, Monad m) => TopLevelGuardDeclr -> m ()
validateGuardDeclr ZeroGuardDeclr = return ()
validateGuardDeclr (SomeGuardDeclr gt) = contextualise gt $ do
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
                                        raise $ GuardTypeMultipleOccurrences n (Just (show gt))
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

-- |Assuming the guard conforms to a parent guard type, checks
-- if the guard matches the given (sub)guard type declaration.
matchesGuardDeclr :: GuardDeclr -> Guard v -> Bool
matchesGuardDeclr (NamedGD _ n) (GD g) = Map.member n g
matchesGuardDeclr (PermissionGD _ n) (GD g) = Map.member n g
matchesGuardDeclr (ProductGD _ t1 t2) g = matchesGuardDeclr t1 g || matchesGuardDeclr t2 g
matchesGuardDeclr (SumGD _ t1 t2) g = matchesGuardDeclr t1 g || matchesGuardDeclr t2 g


guardEquivalence :: GuardDeclr -> Guard v1 -> Guard v2 -> (Guard v3, Guard v4)
-- ^Given a 'GuardDeclr' and a pair of guards, find a pair of guards that
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
                        ma = matchesGuardDeclr
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

guardEntailmentTL :: (MonadPlus m, MonadState s m, AssertionLenses s,
        MonadLogger m) =>
                TopLevelGuardDeclr -> Guard VariableID -> Guard VariableID ->
                        m (Guard VariableID)
guardEntailmentTL ZeroGuardDeclr _ _ = return emptyGuard
guardEntailmentTL (SomeGuardDeclr gt) g1 g2 = guardEntailment gt g1 g2

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

-- |Compute an underapproximation of the least upper bound of two guards.
-- That is, compute a guard that is guaranteed to be entailed by the least
-- guard that entails both of the provided guards.
--
-- PRECONDITION: the guards match the guard type declaration, and the declaration is valid
conservativeGuardLUB :: (MonadState s m, AssumptionLenses s) =>
        GuardDeclr -> Guard VariableID -> Guard VariableID -> m (Guard VariableID)
conservativeGuardLUB (NamedGD _ n) g1@(GD g1m) g2 = return $ if Map.member n g1m then g1 else g2
conservativeGuardLUB (PermissionGD _ n) g1@(GD g1m) g2@(GD g2m) =
                            case (Map.lookup n g1m, Map.lookup n g2m) of
                                (Nothing, _) -> return g2
                                (_, Nothing) -> return g1
                                (Just (PermissionGP p1), Just (PermissionGP p2)) -> do
                                    p <- liftM var $ newAvar ("p_" ++ n)
                                    assumeTrue $ PALte p1 p
                                    assumeTrue $ PALte p2 p
                                    return (GD $ Map.singleton n (PermissionGP p))
                                _ -> error "conservativeGuardLUB: guard does not match expected type."
conservativeGuardLUB (ProductGD _ gd1 gd2) g1 g2 = do
                            (GD gg1) <- conservativeGuardLUB gd1 (res gd1 g1) (res gd1 g2)
                            (GD gg2) <- conservativeGuardLUB gd2 (res gd2 g1) (res gd2 g2)
                            -- Since the guard delcrs are well-formed, gg1 and gg2 won't share keys
                            return $ GD $ Map.union gg1 gg2
                    where
                        res gd (GD g) = GD $ Map.intersection g (gdnames gd) 
                        gdnames (NamedGD _ n) = Map.singleton n ()
                        gdnames (PermissionGD _ n) = Map.singleton n ()
                        gdnames (ProductGD _ gda gdb) = Map.union (gdnames gda) (gdnames gdb)
                        gdnames (SumGD _ gda gdb) = Map.union (gdnames gda) (gdnames gdb)
conservativeGuardLUB (SumGD _ gd1 gd2) g1 g2 = 
                case (ma gd1 g1, ma gd2 g1, ma gd1 g2, ma gd2 g2) of
                    (True, False, False, True) -> return $ fullGuard $ toWeakGuardType gd1
                    (False, True, True, False) -> return $ fullGuard $ toWeakGuardType gd1
                    (True, False, True, False) -> conservativeGuardLUB gd1 g1 g2
                    (False, True, False, True) -> conservativeGuardLUB gd2 g1 g2
                    (_, _, False, False) -> return g1
                    (False, False, _, _) -> return g2
                    _ -> error "conservativeGuardLUB: guard does not match expected type."
        where
            ma = matchesGuardDeclr

-- |Compute an underapproximation of the least upper bound of two guards.
-- That is, compute a guard that is guaranteed to be entailed by the least
-- guard that entails both of the provided guards.
--
-- PRECONDITION: the guards match the guard type declaration, and the declaration is valid
conservativeGuardLUBTL :: (MonadState s m, AssumptionLenses s) =>
        TopLevelGuardDeclr -> Guard VariableID -> Guard VariableID -> m (Guard VariableID)
conservativeGuardLUBTL ZeroGuardDeclr _ _ = return $ emptyGuard
conservativeGuardLUBTL (SomeGuardDeclr gd) g1 g2 = conservativeGuardLUB gd g1 g2