-- TODO: Clean up and properly document
{-# LANGUAGE RankNTypes, MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances, TypeSynonymInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# OPTIONS_GHC -Wall #-}
-- We should use explicit exports

module Caper.Guards(
  Guard(..),
  GuardParameters(..),
  WeakGuardType,
  topLevelToWeakGuardType,
  fullGuard,
  checkGuardAtType,
  toWeakGuardType,
  validateGuardDeclr,
  conservativeGuardLUBTL,
  guardEntailmentTL
)  where

import Prelude hiding (mapM,sequence,foldl,mapM_,concatMap,foldr)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Control.Monad hiding (mapM,sequence)
import Data.Foldable
import Data.Traversable
import Data.List (intercalate)
import Control.Monad.State hiding (mapM_,mapM,sequence)
import Control.Monad.Reader hiding (mapM_,mapM,sequence)
import Control.Lens hiding (op)

import Caper.Parser.AST.Annotation (GuardDeclr(..), TopLevelGuardDeclr(..))
import Caper.Logger
import Caper.ProverDatatypes
import Caper.Prover
import Caper.ProverStates
import Caper.Utils.NondetClasses
import Caper.Utils.Mix
import Caper.Exceptions



data GuardParameterType =
                UniqueGPT
                | PermissionGPT
                | ValueGPT
--                | CountingGPT
                deriving (Eq,Ord,Show)

-- INVARIANT : instances of WeakGuardType must be non-empty
type WeakGuardType = Set.Set (Map.Map String GuardParameterType)

-- | Checks that each guard name occurs once - this is needed to ensure consitency of Capers internal representation
validateGuardDeclr :: (MonadRaise m, Monad m) => TopLevelGuardDeclr -> m ()
validateGuardDeclr ZeroGuardDeclr = return ()
validateGuardDeclr (SomeGuardDeclr gt) = contextualise gt $ do
                        _ <- vgt Set.empty gt
                        return ()
        where
                vgt s (NamedGD _ n) = checkFresh s n
                vgt s (PermissionGD _ n) = checkFresh s n
                vgt s (ParametrisedGD _ n) = checkFresh s n
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
toWeakGuardType (ParametrisedGD _ n) = Set.singleton $ Map.singleton n ValueGPT
toWeakGuardType (ProductGD _ gt1 gt2) = mixWith Map.union (toWeakGuardType gt1) (toWeakGuardType gt2)
toWeakGuardType (SumGD _ gt1 gt2) = Set.union (toWeakGuardType gt1) (toWeakGuardType gt2)

topLevelToWeakGuardType :: TopLevelGuardDeclr -> WeakGuardType
topLevelToWeakGuardType ZeroGuardDeclr = Set.singleton Map.empty
topLevelToWeakGuardType (SomeGuardDeclr gt) = toWeakGuardType gt


-- Unique, Permissisons, Parameterised, Counting... 
data GuardParameters v = NoGP | PermissionGP (PermissionExpression v)
    | ParameterGP (SetExpression v) 
-- | CountingGP (ValueExpression v), from ProverDatatypes
        deriving (Show,Eq,Ord,Functor,Foldable,Traversable)

instance FreeVariables (GuardParameters v) v where
  foldrFree f x NoGP = x
  foldrFree f x (PermissionGP pe) = foldr f x pe
  foldrFree f x (ParameterGP s) = foldrFree f x s

newtype Guard v = GD (Map.Map String (GuardParameters v)) deriving (Eq,Ord,Functor,Foldable,Traversable)

instance FreeVariables (Guard v) v where
  foldrFree f x (GD mp) = Map.foldr (flip $ foldrFree f) x mp

emptyGuard :: Guard v
emptyGuard = GD Map.empty

instance Show v => Show (Guard v) where
        show (GD mp) = doshow (Map.toList mp)
                where
                        doshow [] = "0"
                        doshow ll = intercalate " * " (map showone ll)
                        showone (s, NoGP) = s
                        showone (s, PermissionGP perm) = s ++ "[" ++ show perm ++ "]"
                        showone (s, ParameterGP st) = s ++ show st 


-- Probably to be pruned
guardLift :: (Map.Map String (GuardParameters t)
               -> Map.Map String (GuardParameters v))
               -> Guard t -> Guard v
guardLift f (GD x) = GD (f x)

instance ExpressionCASub GuardParameters Expr where
    exprCASub _ NoGP = NoGP
    exprCASub s (PermissionGP pe) = PermissionGP (exprSub s pe)
    exprCASub s (ParameterGP st) = ParameterGP (exprCASub s st)
    exprCASub' _ NoGP = NoGP
    exprCASub' s (PermissionGP pe) = PermissionGP (exprSub s pe)
    exprCASub' s (ParameterGP st) = ParameterGP (exprCASub' s st)

instance ExpressionCASub Guard Expr where
    exprCASub s (GD g) = GD $ Map.map (exprCASub s) g
    exprCASub' s (GD g) = GD $ Map.map (exprCASub' s) g

checkGuardAtType :: Guard v -> WeakGuardType -> Bool
checkGuardAtType (GD g)
  = Set.fold (\ m b -> b || Map.foldWithKey (matchin m) True g) False
        where
                matchin m k p b = b && case Map.lookup k m of
                                Nothing -> False
                                (Just x) -> matchup p x
                matchup NoGP UniqueGPT = True
                matchup (PermissionGP _) PermissionGPT = True
                matchup (ParameterGP _) ValueGPT = True
                matchup _ _ = False

-- Possibly rename to something more sensible?
gtToG :: StringVariable v => GuardParameterType -> GuardParameters v
gtToG UniqueGPT = NoGP
gtToG PermissionGPT = PermissionGP PEFull
gtToG ValueGPT = ParameterGP fullSet

fullGuard :: StringVariable v => WeakGuardType -> Guard v
fullGuard gt = GD $ Map.map gtToG (Set.findMin gt)

-- Possibly not used anywhere
fullGuards :: StringVariable v => WeakGuardType -> [Guard v]
fullGuards = Prelude.map (GD . Map.map gtToG) . Set.toList

-- not exported
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
                                                assumeTrue $ PADis perm1 perm2
                                                return $ PermissionGP $ PESum perm1 perm2
                                        (ParameterGP s1, ParameterGP s2) -> do
                                                -- Assume the intersection is empty (disjointness)
                                                assumeTrue $ SubsetEq (setIntersection s1 s2) emptySet
                                                -- and return the union
                                                return $ ParameterGP $ setUnion s1 s2
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
matchesGuardDeclr (ParametrisedGD _ n) (GD g) = Map.member n g
matchesGuardDeclr (ProductGD _ t1 t2) g = matchesGuardDeclr t1 g || matchesGuardDeclr t2 g
matchesGuardDeclr (SumGD _ t1 t2) g = matchesGuardDeclr t1 g || matchesGuardDeclr t2 g

-- We want to determine g_1 |?- g_2. We do so by finding g_1' ~ g_2' and checking whether
-- g1 |- g1' * f and g2' * f |- g2 where the latter is non-key-changing entailments.
guardEquivalence :: StringVariable v => GuardDeclr -> Guard v -> Guard v -> (Guard v, Guard v)
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
                        -- fgf :: GuardDeclr -> Guard v -> Guard w
                        -- fullGuardFor, needs a counting clause
                        fgf (NamedGD _ n) _ = GD $ Map.singleton n NoGP
                        fgf (PermissionGD _ n) _ = GD $ Map.singleton n (PermissionGP PEFull)
                        fgf (ParametrisedGD _ n) _ = GD $ Map.singleton n (ParameterGP fullSet)
                        fgf (ProductGD _ gt1 gt2) g = guardJoin (fgf gt1 g) (fgf gt2 g)
                        fgf (SumGD _ gt1 gt2) g = if ma gt2 g then fgf gt2 g else fgf gt1 g
guardEquivalence _ _ _ = (GD Map.empty, GD Map.empty)

-- Relocate closer to use-site. 
sameGuardParametersType :: GuardParameters v -> GuardParameters w -> Maybe (GuardParameters v)
sameGuardParametersType NoGP NoGP = Nothing
sameGuardParametersType (PermissionGP _) (PermissionGP _) = Nothing
sameGuardParametersType (ParameterGP _) (ParameterGP _) = Nothing
sameGuardParametersType a _ = Just a

class (MonadIO m, MonadPlus m, MonadOrElse m, MonadState s m, AssertionLenses s, MonadLogger m,
    MonadReader r m, Provers r, DebugState s r, MonadLabel CapturedState m) => GuardCheckMonad s r m
instance (MonadIO m, MonadPlus m, MonadOrElse m, MonadState s m, AssertionLenses s, MonadLogger m,
    MonadReader r m, Provers r, DebugState s r, MonadLabel CapturedState m) => GuardCheckMonad s r m

subtractPE :: GuardCheckMonad s r m =>
        PermissionExpression VariableID -> PermissionExpression VariableID ->
                m (Maybe (PermissionExpression VariableID))
subtractPE l PEFull = do
                        assertTrue $ PAEq l PEFull
                        return Nothing
subtractPE l PEZero = return (Just l)
subtractPE l s = (do -- TODO: frame some permission
                assertTrue $ PAEq l s
                justCheck -- is this a good idea to have? Maybe some profiling could reveal whether failing earlier is a win.
                labelS $ "Take whole permissions guard: " ++ show s ++ "=" ++ show l
                return Nothing) `mplus`
        (do
                ev <- newEvar "perm"
                let eve = PEVar ev
                assertTrue $ PAEq l (PESum s eve)
                labelS $ "Frame permission: " ++ show s ++ " + " ++ show eve ++ "=" ++ show l
                return (Just eve))

-- |Given a guard parameter we have, take away a given guard parameter.
-- If things are of the wrong type, backtrack rather than erroring, because
-- we might just have picked the wrong region.
subtractGP :: (GuardCheckMonad s r m) =>
        GuardParameters VariableID -> GuardParameters VariableID ->
                m (Maybe (GuardParameters VariableID))
subtractGP NoGP NoGP = return Nothing
subtractGP (PermissionGP p1) (PermissionGP p2) =
                liftM (fmap PermissionGP) $ subtractPE p1 p2
subtractGP (ParameterGP s1) (ParameterGP s2) = do
                assertTrue $ SubsetEq s2 s1
                return $ Just $ ParameterGP $ setDifference s1 s2
subtractGP _ _ = mzero

guardPrimitiveEntailmentM :: (GuardCheckMonad s r m) =>
                Guard VariableID -> Guard VariableID -> m (Guard VariableID)
guardPrimitiveEntailmentM (GD g1) (GD g2) = if Map.null $ Map.differenceWith sameGuardParametersType g2 g1 then liftM GD doGPEM else mzero
        where
                rest = Map.difference g1 g2
                doGPEM = do
                        let k = Map.intersectionWith (,) g1 g2
                        r <- mapM subtrct k
                        return $ Map.union (Map.mapMaybe id r) rest
                subtrct = uncurry subtractGP
                {- CAN BE DELETED
                subtrct :: (MonadPlus m, MonadState s m, AssertionLenses s,
                        MonadLogger m) =>
                        (GuardParameters VariableID, GuardParameters VariableID) -> m (Maybe (GuardParameters VariableID))
                subtrct (NoGP, NoGP) = return Nothing
                subtrct (PermissionGP pe1, PermissionGP pe2) = liftM (fmap PermissionGP) $ subtractPE pe1 pe2
                subtrct _ = mzero -- Should be impossible
                -}


guardEntailment :: (GuardCheckMonad s r m) =>
                GuardDeclr -> Guard VariableID -> Guard VariableID ->
                        m (Guard VariableID)
guardEntailment gt g1 g2 = 
                        do
                                let (gel, ger) = guardEquivalence gt g1 g2
                                if gel == emptyGuard then guardPrimitiveEntailmentM g1 g2 else do
                                        frame1 <- guardPrimitiveEntailmentM g1 gel
                                        guardPrimitiveEntailmentM (guardJoin frame1 ger) g2

guardEntailmentTL :: (GuardCheckMonad s r m) =>
                TopLevelGuardDeclr -> Guard VariableID -> Guard VariableID ->
                        m (Guard VariableID)
guardEntailmentTL ZeroGuardDeclr _ _ = return emptyGuard
guardEntailmentTL (SomeGuardDeclr gt) g1 g2 = guardEntailment gt g1 g2

-- |Try to extract a single guard resource, where we don't know the guard type.
-- Consequently, no rewriting of guards is possible.
consumeGuardNoType :: (GuardCheckMonad s r m) =>
                String -> GuardParameters VariableID ->
                Guard VariableID -> m (Guard VariableID)
consumeGuardNoType gname gpara (GD g) = do
                        gp <- liftMaybe $ g ^. at gname
                        gp' <- subtractGP gp gpara
                        return $ GD $ at gname .~ gp' $ g

consumeGuard' :: (GuardCheckMonad s r m) =>
                GuardDeclr ->
                String -> GuardParameters VariableID ->
                Guard VariableID -> m (Guard VariableID)
consumeGuard' gt gname gpara g =
                do
                        let (gel, ger) = guardEquivalence gt g
                                (GD $ Map.insert gname gpara Map.empty)
                        if gel == emptyGuard then consumeGuardNoType gname gpara g else do
                                frame1 <- guardPrimitiveEntailmentM g gel
                                consumeGuardNoType gname gpara (guardJoin frame1 ger)

consumeGuard :: (GuardCheckMonad s r m) =>
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
conservativeGuardLUB (ParametrisedGD _ n) g1@(GD g1m) g2@(GD g2m) =
                            case (Map.lookup n g1m, Map.lookup n g2m) of
                                (Nothing, _) -> return g2
                                (_, Nothing) -> return g1
                                (Just (ParameterGP s1), Just (ParameterGP s2)) ->
                                    return $ GD $ Map.singleton n $ ParameterGP $ setUnion s1 s2
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
                        gdnames (ParametrisedGD _ n) = Map.singleton n ()
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
conservativeGuardLUBTL ZeroGuardDeclr _ _ = return emptyGuard
conservativeGuardLUBTL (SomeGuardDeclr gd) g1 g2 = conservativeGuardLUB gd g1 g2
