{-# LANGUAGE RankNTypes, MultiParamTypeClasses, FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveDataTypeable, FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
import Prelude hiding (catch)
import Data.Map as Map
import Data.Set as Set
import Control.Monad.Exception

data PermissionExpression =
                FullPerm
                | VarPerm String
                | EVarPerm String
                | PlusPerm PermissionExpression PermissionExpression
                deriving (Show)

type ValueExpression = ()

-- The empty guard type (ZeroGT) should not be allowed as a 
-- parameter to a sum or product.  We therefore split guard
-- types into two levels.

data TopLevelGuardTypeAST =
                ZeroGT | SomeGT GuardTypeAST

data GuardTypeAST =
                NamedGT String
                | NamedPermissionGT String
                | ParametrisedGT String
                | ProductGT GuardTypeAST GuardTypeAST
                | SumGT GuardTypeAST GuardTypeAST
                deriving (Show)

data GuardTypeException =
                GTEMultipleOccurrence String (Maybe GuardTypeAST)
                deriving Typeable

instance Show GuardTypeException where
        show (GTEMultipleOccurrence s Nothing) = "Multiple guards named \"" ++ s ++ "\" are declared in a guard type."
        show (GTEMultipleOccurrence s (Just gt)) = "Multiple guards named \"" ++ s ++ "\" are declared in the guard type \"" ++ (show gt) ++ "\"."

instance Exception GuardTypeException


data GuardParameterType =
                UniqueGPT | PermissionGPT | ValueGPT
                deriving (Eq,Ord,Show)

-- INVARIANT : instances of WeakGuardType must be non-empty
type WeakGuardType = Set.Set (Map.Map String GuardParameterType)

validateGuardTypeAST :: (Throws GuardTypeException l) => TopLevelGuardTypeAST -> EM l ()
validateGuardTypeAST ZeroGT = return ()
validateGuardTypeAST (SomeGT gt) = do
                        vgt Set.empty gt
                        return ()
        where
                vgt s (NamedGT n) = checkFresh s n
                vgt s (NamedPermissionGT n) = checkFresh s n
                vgt s (ParametrisedGT n) = checkFresh s n
                vgt s (ProductGT gt1 gt2) = do
                                                s1 <- vgt s gt1
                                                vgt s1 gt2
                vgt s (SumGT gt1 gt2) = do
                                                s1 <- vgt s gt1
                                                vgt s1 gt2
                checkFresh s n = do if Set.member n s then throw $ GTEMultipleOccurrence n (Just gt) else return $ Set.insert n s
                
mixWith :: (Ord a, Ord b, Ord c) => (a -> b -> c) -> Set.Set a -> Set.Set b -> Set.Set c
mixWith op s1 s2 = Set.unions $ Set.toList $ Set.map (\x -> Set.map (op x) s2) s1


toWeakGuardType :: GuardTypeAST -> WeakGuardType
toWeakGuardType (NamedGT n) = Set.singleton $ Map.singleton n UniqueGPT
toWeakGuardType (NamedPermissionGT n) = Set.singleton $ Map.singleton n PermissionGPT
toWeakGuardType (ParametrisedGT n) = Set.singleton $ Map.singleton n ValueGPT
toWeakGuardType (ProductGT gt1 gt2) = mixWith Map.union (toWeakGuardType gt1) (toWeakGuardType gt2)
toWeakGuardType (SumGT gt1 gt2) = Set.union (toWeakGuardType gt1) (toWeakGuardType gt2)

topLevelToWeakGuardType :: TopLevelGuardTypeAST -> WeakGuardType
topLevelToWeakGuardType ZeroGT = Set.singleton Map.empty
topLevelToWeakGuardType (SomeGT gt) = toWeakGuardType gt


-- toWeakGuardTypeWorker :: WeakGuardType -> GuardType

data GuardAST =
                EmptyG
                | NamedG String
                | NamedPermissionG String PermissionExpression
                | ParametrisedG String ValueExpression
                | CoParametrisedG String [ValueExpression]
                | StarG GuardAST GuardAST
                deriving (Show)




data GuardException =
                GEInconsistentOccurrences String GuardAST
                deriving Typeable

instance Show GuardException where
        show (GEInconsistentOccurrences s g) = "The guard named \"" ++ s ++ "\" is used inconsistently in the guard expression \"" ++ (show g) ++ "\"."

instance Exception GuardException

data GuardParameters = NoGP | PermissionGP PermissionExpression | Parameters [ValueExpression] | CoParameters [ValueExpression] [ValueExpression]
        deriving (Show)

type Guard = Map.Map String GuardParameters

toGuard :: (Throws GuardException l) => GuardAST -> EM l Guard
toGuard gast = tg (Map.empty) gast
        where
                tg g (EmptyG) = return g
                tg g (NamedG n) = if n `Map.member` g then throw (GEInconsistentOccurrences n gast) else return $ Map.insert n NoGP g
                tg g (NamedPermissionG n pe) = case Map.lookup n g of
                                        (Nothing) -> return $ Map.insert n (PermissionGP pe) g
                                        (Just (PermissionGP pe0)) -> return $ Map.insert n (PermissionGP (PlusPerm pe0 pe)) g
                                        _ -> throw $ GEInconsistentOccurrences n gast
                tg g (ParametrisedG n v) = case Map.lookup n g of
                                        (Nothing) -> return $ Map.insert n (Parameters [v]) g
                                        (Just (Parameters vs)) -> return $ Map.insert n (Parameters (v : vs)) g
                                        (Just (CoParameters vs covs)) -> return $ Map.insert n (CoParameters (v : vs) covs) g
                                        _ -> throw $ GEInconsistentOccurrences n gast
                tg g (CoParametrisedG n vs) = case Map.lookup n g of
                                        (Nothing) -> return $ Map.insert n (CoParameters [] vs) g
                                        (Just (Parameters vs')) -> return $ Map.insert n (CoParameters vs' vs) g
                                        _ -> throw $ GEInconsistentOccurrences n gast
                tg g (StarG ge1 ge2) = do
                                                g' <- tg g ge1
                                                tg g' ge2

checkGuardAtType :: Guard -> WeakGuardType -> Bool
checkGuardAtType g gt = Set.fold (\m b -> b || Map.foldWithKey (matchin m) True g) False gt
        where
                matchin m k p b = b && case Map.lookup k m of
                                Nothing -> False
                                (Just x) -> matchup p x
                matchup NoGP UniqueGPT = True
                matchup (PermissionGP _) PermissionGPT = True
                matchup (Parameters _) ValueGPT = True
                matchup (CoParameters _ _) ValueGPT = True
                matchup _ _ = False

fullGuard :: WeakGuardType -> Guard
fullGuard gt = Map.map gtToG (Set.findMin gt)
        where
                gtToG UniqueGPT = NoGP
                gtToG PermissionGPT = PermissionGP FullPerm
                gtToG ValueGPT = CoParameters [] []
