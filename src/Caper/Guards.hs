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
  strongCheckGuardAtTLType,
  checkGuardAtType,
  toWeakGuardType,
  validateGuardDeclr,
  conservativeGuardLUBTL,
  guardEntailmentTL,
  guardEntailment,
  mergeGuards,
  emptyGuard,
  consumeGuard,
  consumeGuardNoType,
  combineCountingGuard,
  combineParametrisedGuard,
  combinePermissionGuard
)  where
-- import Control.Applicative
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
import Caper.ProverStates
import Caper.Utils.NondetClasses
import Caper.Utils.Mix
import Caper.Exceptions


data GuardParameterType =
    UniqueGPT
  | PermissionGPT
  | ValueGPT
  | CountingGPT  
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
                vgt s (CountingGD _ n) = checkFresh s n
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
toWeakGuardType (CountingGD _ n) = Set.singleton $ Map.singleton n CountingGPT

topLevelToWeakGuardType :: TopLevelGuardDeclr -> WeakGuardType
topLevelToWeakGuardType ZeroGuardDeclr = Set.singleton Map.empty
topLevelToWeakGuardType (SomeGuardDeclr gt) = toWeakGuardType gt


-- Unique, Permissisons, Parameterised, Counting... 
data GuardParameters v = NoGP
                       | PermissionGP (PermissionExpression v)
                       | ParameterGP (SetExpression v) 
                       | CountingGP (ValueExpression v)
                       deriving (Show,Eq,Ord,Functor,Foldable,Traversable)

instance FreeVariables (GuardParameters v) v where
  foldrFree _ x NoGP = x
  foldrFree f x (PermissionGP pe) = foldr f x pe
  foldrFree f x (ParameterGP s) = foldrFree f x s
  foldrFree f x (CountingGP v) = foldr f x v

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
                        showone (s, CountingGP v) = s ++ "|" ++ show v ++ "|"

instance ExpressionCASub GuardParameters Expr where
    exprCASub _ NoGP = NoGP
    exprCASub s (PermissionGP pe) = PermissionGP (exprSub s pe)
    exprCASub s (ParameterGP st) = ParameterGP (exprCASub s st)
    exprCASub s (CountingGP v) = CountingGP (exprSub s v) --TODO(kja): Sanity Check

    exprCASub' _ NoGP = NoGP
    exprCASub' s (PermissionGP pe) = PermissionGP (exprSub s pe)
    exprCASub' s (ParameterGP st) = ParameterGP (exprCASub' s st)
    exprCASub' s (CountingGP v) = CountingGP (exprSub s v) -- TODO(kja): Sanity check

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
                matchup (CountingGP _) CountingGPT =  True
                matchup _ _ = False

basicGuardTypeCheck :: Guard v -> GuardDeclr -> Bool
basicGuardTypeCheck (GD grd0) gdclr = case (do
                    when (Map.null grd0) (Left True)
                    chk gdclr grd0)
                of
                    Left True -> True
                    _ -> False
    where
        takeKey = Map.updateLookupWithKey (\_ _ -> Nothing)
        chk (NamedGD _ n) grd = let (res, grd') = takeKey n grd in
                case res of
                    Nothing -> Right grd
                    Just NoGP -> if Map.null grd' then Left True else Right grd'
                    _ -> Left False
        chk (PermissionGD _ n) grd = let (res, grd') = takeKey n grd in
                case res of
                    Nothing -> Right grd
                    Just (PermissionGP _) -> if Map.null grd' then Left True else Right grd'
                    _ -> Left False
        chk (ParametrisedGD _ n) grd = let (res, grd') = takeKey n grd in
                case res of
                    Nothing -> Right grd
                    Just (ParameterGP _) -> if Map.null grd' then Left True else Right grd'
                    _ -> Left False
        chk (ProductGD _ gt1 gt2) grd = chk gt1 grd >>= chk gt2
        chk (SumGD _ gt1 gt2) grd = chk gt1 grd >>= chk gt2
        chk (CountingGD _ n) grd = let (res, grd') = takeKey n grd in
                case res of
                    Nothing -> Right grd
                    Just (CountingGP _) -> if Map.null grd' then Left True else Right grd'
                    _ -> Left False

-- |Check that a guard conforms to the guard declaration, allowing for
-- "neutral elements" -- i.e. G[0p], G|0| when they are allowed by the
-- guard declaration.
strongCheckGuardAtType :: (MonadState s m, AssumptionLenses s, MonadDemonic m, MonadReader r m, DebugState s r, MonadLabel CapturedState m) =>
                Guard VariableID -> GuardDeclr -> m ()
strongCheckGuardAtType grd@(GD g) dec = do
        unless (basicGuardTypeCheck grd dec) succeed
        let wkgt = toWeakGuardType dec
        let conds0 = Set.foldr genConds (Just []) wkgt
        case conds0 of
            Nothing -> return ()
            Just conds -> do
                dAll [mapM_ assumeTrue cond >> labelS ("Guard type empty case: " ++ show cond) | cond <- conds]
    where
        genConds :: Map.Map String GuardParameterType -> Maybe [[Condition VariableID]] -> Maybe [[Condition VariableID]]
        genConds wgt cs = do
                let intr = Map.intersection g wgt
                let diff = Map.difference g wgt
                guard $ not $ Map.null diff
                if Map.null intr then cs
                    else case diffZero diff of
                        Nothing -> cs
                        Just c -> (c :) <$> cs
        diffZero :: Map.Map String (GuardParameters VariableID) -> Maybe [Condition VariableID]
        -- Determines conditions for all the guards to be zero.
        -- Nothing means this is impossible.
        diffZero = foldr (combine . gpUnitCond) (Just [])
        combine l r = (:) <$> l <*> r
        gpUnitCond :: GuardParameters VariableID -> Maybe (Condition VariableID)
        gpUnitCond NoGP = Nothing
        gpUnitCond (PermissionGP pe) = Just $ toCondition $ PAEq pe PEZero
        gpUnitCond (ParameterGP s) = Just $ toCondition $ SubsetEq s emptySet
        gpUnitCond (CountingGP v) = Just $ toCondition $ VAEq v (VEConst 0)

strongCheckGuardAtTLType :: (MonadState s m, AssumptionLenses s, MonadDemonic m, MonadReader r m, DebugState s r, MonadLabel CapturedState m) =>
                Guard VariableID -> TopLevelGuardDeclr -> m ()
strongCheckGuardAtTLType (GD g) ZeroGuardDeclr = unless (Map.null g) succeed
strongCheckGuardAtTLType gd (SomeGuardDeclr gt) = strongCheckGuardAtType gd gt

gtToG :: StringVariable v => GuardParameterType -> GuardParameters v
gtToG UniqueGPT = NoGP
gtToG PermissionGPT = PermissionGP PEFull
gtToG ValueGPT = ParameterGP fullSet
gtToG CountingGPT = CountingGP $ VEConst (-1)

fullGuard :: StringVariable v => WeakGuardType -> Guard v
fullGuard gt = GD $ Map.map gtToG (Set.findMin gt)

-- not exported
guardJoin :: Guard v -> Guard v -> Guard v
guardJoin (GD g1) (GD g2) = GD $ Map.union g1 g2

combineCountingGuard ::  ValueExpression v -> ValueExpression v -> (GuardParameters v, Condition v)
combineCountingGuard n m = (gp, cond)
  where
    cond = toCondition $
      ((VEConst 0 $<=$ n) `FOFAnd` (VEConst 0 $<=$ m))
      `FOFOr` ((n $<$ VEConst 0) `FOFAnd` (VEConst 0 $<=$ m) `FOFAnd` (n $+$ m $<$ VEConst 0))
      `FOFOr` ((m $<$ VEConst 0) `FOFAnd` (VEConst 0 $<=$ n) `FOFAnd` (n $+$ m $<$ VEConst 0))
    gp = CountingGP $ n $+$ m

combineParametrisedGuard :: (Refreshable v, StringVariable v, Ord v) => SetExpression v -> SetExpression v -> (GuardParameters v, Condition v)
combineParametrisedGuard s1 s2 = (gp, cond)
  where
    cond = toCondition $ SubsetEq (setIntersection s1 s2) emptySet
    gp = ParameterGP $ setUnion s1 s2

combinePermissionGuard :: PermissionExpression v -> PermissionExpression v -> (GuardParameters v, Condition v)
combinePermissionGuard p1 p2 = (gp, cond)
  where
    cond = toCondition $ PADis p1 p2
    gp = PermissionGP $ PESum p1 p2

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
                                          let (combined, condition) = combinePermissionGuard perm1 perm2
                                          assumeTrue condition
                                          return combined
                                        (ParameterGP s1, ParameterGP s2) -> do
                                          let (combined, condition) = combineParametrisedGuard s1 s2
                                          assumeTrue condition
                                          return combined
                                        (CountingGP n, CountingGP m) -> do
                                          let (combined, condition) = combineCountingGuard n m
                                          assumeTrue condition
                                          return combined
                                        _ -> do
                                          assumeContradiction
                                          -- Since we've assumed false, it shouldn't
                                          -- matter what we return here...
                                          return v1

-- |Assuming the guard conforms to a parent guard type, checks
-- if the guard (potentially) matches the given (sub)guard type declaration.
matchesGuardDeclr :: GuardDeclr -> Guard v -> Bool
matchesGuardDeclr (NamedGD _ n) (GD g) = Map.member n g
matchesGuardDeclr (PermissionGD _ n) (GD g) = Map.member n g
matchesGuardDeclr (ParametrisedGD _ n) (GD g) = Map.member n g
matchesGuardDeclr (ProductGD _ t1 t2) g = matchesGuardDeclr t1 g || matchesGuardDeclr t2 g
matchesGuardDeclr (SumGD _ t1 t2) g = matchesGuardDeclr t1 g || matchesGuardDeclr t2 g
matchesGuardDeclr (CountingGD _ n) (GD g) = Map.member n g

-- We want to determine g_1 |?- g_2. We do so by finding g_1' ~ g_2' and checking whether
-- g1 |- g1' * f and g2' * f |- g2 where the latter is non-key-changing entailments.

-- XXX: I'm not entirely sure this is going to be OK...
guardEquivalences :: (MonadPlus m, StringVariable v) => GuardDeclr -> Guard v -> Guard v -> m (Guard v, Guard v)
-- ^Given a 'GuardDeclr' and a pair of guards, find a pairs of guards that
-- could be used to rewrite the first to entail the second.
-- This assumes the guards conform to the guard type.
-- (This operation is non-deterministic to allow for a guard matching the
-- guard type in more than one way, for instance, if there are components
-- that are empty, but not represented by the empty map (e.g. G[0p]).)
guardEquivalences (ProductGD _ gta1 gta2) gd1 gd2 = do
                (gd3a, gd4a) <- guardEquivalences gta1 gd1 gd2
                (gd3b, gd4b) <- guardEquivalences gta2 gd1 gd2
                return (guardJoin gd3a gd3b, guardJoin gd4a gd4b)
guardEquivalences (SumGD _ gta1 gta2) gd1 gd2 = msum $
                                        [guardEquivalences gta1 gd1 gd2 | m11, m12] ++
                                        [return (fg1, fg2) | m11, m22, fg1 <- fgf gta1 gd1, fg2 <- fgf gta2 gd2] ++
                                        [guardEquivalences gta2 gd1 gd2 | m21, m22] ++
                                        [return (fg1, fg2) | m21, m12, fg1 <- fgf gta2 gd1, fg2 <- fgf gta1 gd2] ++
                                        [return (GD Map.empty, GD Map.empty) | (not (m11 && m12) && not (m21 && m22))]
                where
                        ma = matchesGuardDeclr
                        m11 = ma gta1 gd1
                        m12 = ma gta1 gd2
                        m21 = ma gta2 gd1
                        m22 = ma gta2 gd2
                        fgf (NamedGD _ n) _ = return $ GD $ Map.singleton n NoGP
                        fgf (PermissionGD _ n) _ = return $ GD $ Map.singleton n (PermissionGP PEFull)
                        fgf (ParametrisedGD _ n) _ = return $ GD $ Map.singleton n (ParameterGP fullSet)
                        fgf (CountingGD _ n) _ = return $ GD $ Map.singleton n $ CountingGP $ VEConst (-1)
                        fgf (ProductGD _ gt1 gt2) g = guardJoin <$> (fgf gt1 g) <*> (fgf gt2 g)
                        fgf (SumGD _ gt1 gt2) g = (guard (ma gt1 g || (not $ ma gt2 g)) >> fgf gt1 g) `mplus` (guard (ma gt2 g) >> fgf gt2 g)
guardEquivalences _ _ _ = return (GD Map.empty, GD Map.empty)


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
subtractPE l s = (do
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
subtractGP (CountingGP n) (CountingGP m) = do
  f <- VEVar <$> newEvar "f"
  assertTrue . toCondition $
    (FOFAtom $ n `VAEq` (m $+$ f))
    `FOFAnd` ((VEConst 0 $<=$ n) `FOFImpl` ((VEConst 0 $<=$ m) `FOFAnd` (VEConst 0 $<=$ f)))
    `FOFAnd` ((n $<$ VEConst 0) `FOFImpl` ((VEConst 0 $<=$ m) `FOFOr` (VEConst 0 $<=$ f)))
  return $ Just $ CountingGP f
subtractGP _ _ = mzero

sameGuardParametersType :: GuardParameters v -> GuardParameters w -> Maybe (GuardParameters v)
sameGuardParametersType NoGP NoGP = Nothing
sameGuardParametersType (PermissionGP _) (PermissionGP _) = Nothing
sameGuardParametersType (ParameterGP _) (ParameterGP _) = Nothing
sameGuardParametersType (CountingGP _) (CountingGP _) = Nothing
sameGuardParametersType a _ = Just a

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

guardEntailment :: (GuardCheckMonad s r m) =>
                GuardDeclr -> Guard VariableID -> Guard VariableID ->
                        m (Guard VariableID)
guardEntailment gt g1 g2 = 
                        do
                                (gel, ger) <- guardEquivalences gt g1 g2
                                if gel == emptyGuard then (do
                                        labelS $ "No guard rewrite"
                                        guardPrimitiveEntailmentM g1 g2)
                                  else do
                                        labelS $ "Rewrite guard " ++ show g1 ++ " to " ++ show g2
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
                        (gel, ger) <- guardEquivalences gt g
                                (GD $ Map.insert gname gpara Map.empty)
                        if gel == emptyGuard then do
                                labelS $ "No guard rewrite"
                                consumeGuardNoType gname gpara g
                            else do
                                labelS $ "Rewrite guard " ++ show gel ++ " to " ++ show ger
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
                        gdnames (CountingGD _ n) = Map.singleton n ()
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
conservativeGuardLUB (CountingGD _ n)  g1@(GD g1m) g2@(GD g2m) =
                            case (Map.lookup n g1m, Map.lookup n g2m) of
                                (Nothing, _) -> return g2
                                (_, Nothing) -> return g1
                                (Just (CountingGP e1), Just (CountingGP e2)) -> do
                                    k <- liftM var $ newAvar ("k_" ++ n)
                                    assumeTrue $ FOFImpl
                                      (VEConst 0 $<=$ e1)
                                      (FOFOr (k $<$ VEConst 0)
                                             (e1 $<=$ k))
                                    assumeTrue $ FOFImpl
                                      (e1 $<$ VEConst 0)
                                      (FOFAnd (k $<$ VEConst 0)
                                              (e1 $<=$ k))
                                    assumeTrue $ FOFImpl
                                      (VEConst 0 $<=$ e2)
                                      (FOFOr (k $<$ VEConst 0)
                                             (e2 $<=$ k))
                                    assumeTrue $ FOFImpl
                                      (e2 $<$ VEConst 0)
                                      (FOFAnd (k $<$ VEConst 0)
                                              (e2 $<=$ k))                                    
                                    return (GD $ Map.singleton n (CountingGP k))
                                _ -> error "conservativeGuardLUB: guard does not match expected type."

-- |Compute an underapproximation of the least upper bound of two guards.
-- That is, compute a guard that is guaranteed to be entailed by the least
-- guard that entails both of the provided guards.
--
-- PRECONDITION: the guards match the guard type declaration, and the declaration is valid
conservativeGuardLUBTL :: (MonadState s m, AssumptionLenses s) =>
        TopLevelGuardDeclr -> Guard VariableID -> Guard VariableID -> m (Guard VariableID)
conservativeGuardLUBTL ZeroGuardDeclr _ _ = return emptyGuard
conservativeGuardLUBTL (SomeGuardDeclr gd) g1 g2 = conservativeGuardLUB gd g1 g2
