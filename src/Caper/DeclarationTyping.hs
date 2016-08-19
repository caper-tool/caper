{-# LANGUAGE FlexibleContexts, ScopedTypeVariables, MultiParamTypeClasses #-}
module Caper.DeclarationTyping (
        typeDeclarations
) where

import Prelude hiding (mapM_,foldl,elem)
import qualified Data.Map as Map
import Data.Map(Map)
import Data.Maybe(isNothing)
import Data.Foldable
import Control.Monad.State hiding (mapM_)
import Data.List hiding (foldl,elem)
import Control.Lens hiding (pre)

-- import Debug.Trace

import Caper.Logger
import Caper.Parser.AST
import qualified Caper.TypingContext as TC
import Caper.ProverDatatypes
import Caper.Exceptions
import Caper.Utils.SimilarStrings


data Typed = RegPar String Int | PredPar String Int | Local String
        deriving (Eq, Ord)

type TypingState = (Map String Int, Map String Int, TC.TContext Typed VariableType)

initialTypingState :: TypingState
initialTypingState = (Map.empty, Map.empty, TC.empty)

tsPredicateArities :: Simple Lens TypingState (Map String Int)
tsPredicateArities = _1

tsRegionTypeArities :: Simple Lens TypingState (Map String Int)
tsRegionTypeArities = _2

tsContext :: Simple Lens TypingState (TC.TContext Typed VariableType)
tsContext = _3

-- |List of free variables
freeL :: (FreeVariables t v, Eq v) => t -> [v]
freeL = foldrFree (:) []

-- |'TC.bind', but with a specilised type signature for Either
bindE :: (Ord v, Eq t) =>
        v -> t -> TC.TContext v t ->
        Either (TC.TypeUnificationException v t) (TC.TContext v t)
bindE = TC.bind

-- |Try to bind a variable to a type in a state context, possibly raising an
-- exception
bindR :: (MonadState TypingState m, MonadRaise m) =>
        Typed -> VariableType -> m ()
bindR key val = 
         use tsContext >>= liftTUMismatch . bindE key val >>= assign tsContext >> return ()

-- |'TC.unify', but specialised for Either
unifyE :: (Ord v, Eq t) => 
        v -> v -> TC.TContext v t -> 
        Either (TC.TypeUnificationException v t) (TC.TContext v t)
unifyE = TC.unify

-- |Try to unify the types of two variables in a state context, possibly
-- raising an exception.
unifyR :: (MonadState TypingState m, MonadRaise m) =>
        Typed -> Typed -> m ()
unifyR k1 k2 =
        use tsContext >>= liftTUMismatch . unifyE k1 k2 >>= assign tsContext >> return ()

type RegionTyping = Map String [(String, VariableType)]
type PredicateTyping = Map String [(Maybe String, VariableType)]

lTypeToVariableType :: LType -> VariableType
lTypeToVariableType LTInt = VTValue
lTypeToVariableType LTPerm = VTPermission
lTypeToVariableType LTRid = VTRegionID


{- |Determine the parameter typing for the given declarations.
   An exception can occur if the type is overspecified (i.e. a variable
   is used at inconsistent types).  If the type is underspecified, it defaults
   to Value, and a warning is logged.
   An exception will also occur if multiple declarations are given for
   the same name.
-}
typeDeclarations :: (MonadLogger m, MonadRaise m) =>
        [Declr] -> m (PredicateTyping, RegionTyping)
typeDeclarations decs = do
        ts <- flip execStateT initialTypingState $ do
                mapM_ checkArityAndDeclaredTypes decs
                mapM_ typeRegionDeclaration (regionDeclrs decs)
        pt <- foldlM (genPT (ts ^. tsContext)) Map.empty (predicateDeclrs decs)
        rt <- foldlM (genRT (ts ^. tsContext)) Map.empty (regionDeclrs decs)
        return (pt, rt)
    where
        genPT tc m dec@(PredicateDeclr _ pname pparas) = contextualise dec $ do
                tsp <- iforM pparas $ \i (TVarExpr ve _) -> do
                        let v = case ve of
                                Variable _ s -> Just s
                                _ -> Nothing
                        case TC.lookup (PredPar pname i) tc of
                                TC.JustType t -> return (v, t)
                                TC.Undetermined -> do
                                        contextualise ve $ logEvent $
                                            WarnUnconstrainedParameter (show ve) VTValue
                                        return (v, VTValue) 
                                _ -> error $ "typeDeclarations: parameter '"
                                        ++ (show ve) ++ "' of predicate '"
                                        ++ pname ++ "' has no type."
                return $ Map.insert pname tsp m
        genRT tc m dec@(RegionDeclr _ rtname rtparas _ _ _) = contextualise dec $ do
                tsp <- iforM rtparas $ \i v -> do
                        case TC.lookup (RegPar rtname i) tc of
                                TC.JustType t -> return (v, t)
                                TC.Undetermined -> do
                                        logEvent $
                                            WarnUnconstrainedParameter v VTValue
                                        return (v, VTValue)
                                _ -> error $ "typeDeclarations: parameter '"
                                        ++ v ++ "' of region type '"
                                        ++ rtname ++ "'has no type."
                return $ Map.insert rtname tsp m

checkArityAndDeclaredTypes :: (MonadLogger m, MonadRaise m, MonadState TypingState m) =>
        Declr -> m ()
checkArityAndDeclaredTypes dec@(DeclrReg (RegionDeclr _ rtname rparas _ _ _)) =
        contextualise dec $ do
                -- Check if an arity is already given
                oldArity <- use (tsRegionTypeArities . at rtname)
                case oldArity of
                        Just _ -> raise $ OverloadedRegionType rtname
                        Nothing -> do
                                -- if not, set the arity
                                let pcount = length rparas
                                tsRegionTypeArities %= Map.insert rtname pcount
                                -- declare the region types
                                tsContext %= TC.declareAll [RegPar rtname n | n <- [0..pcount - 1]]
                                -- and set the type of the first parameter as rid
                                bindR (RegPar rtname 0) VTRegionID
checkArityAndDeclaredTypes dec@(DeclrPred (PredicateDeclr _ pname pparas)) =
        contextualise dec $ do
                -- Check if an arity is already given
                let pcount = length pparas
                oldArity <- use (tsPredicateArities . at pname)
                if isNothing oldArity || (oldArity == Just pcount) then
                        do
                                tsPredicateArities %= Map.insert pname pcount
                                iforM_ pparas $ \n (TVarExpr ve ot) -> contextualise ve $ case ot of
                                        Nothing -> tsContext %= TC.declare (PredPar pname n)
                                        Just typ -> bindR (PredPar pname n) (lTypeToVariableType typ)
                        else
                                raise $ OverloadedPredicate pname
checkArityAndDeclaredTypes _ = return ()

{-
typeDeclarations decs0 = do
                let rdecs = regionDeclrs decs0 
                let rdecCounts = foldlM rdecCount Map.empty rdecs
                let tc0 = ifoldl initialRDec TC.empty rdecCounts
                let pdecs = predicateDeclrs decs0
                let tc1 = foldl initialPDec tc0 pdecs
                let pdecCounts = foldl pdecCount Map.empty pdecs
                tc <- flip execStateT tc0 $
                                mapM_ (typeDeclaration rdecCounts) decs
                pt <- undefined
                rt <- foldlM (tdm tc) Map.empty decs
                return (pt, rt)
        where
                rdecCount m (RegionDeclr _ rtname rparas _ _ _) = do
                        let (old, m') = Map.insertLookupWithKey (\_ x _ -> x) rtname (length rparas) m
                        if (isJust old) then
                                raise $ OverloadedRegionType rtname
                                else return m'
                pdecCount m (ParameterDeclr _ pname pparas) =
                        Map.insert p (length pparas) m
                tdm tc m dc@(RegionDeclr _ rtname rparas _ _ _) = 
                    contextualise dc $ do
                        pts <- iforM rparas $ \i nm ->
                                case TC.lookup (Left (rtname, i)) tc of
                                    TC.JustType t -> return (nm, t)
                                    TC.Undetermined -> do
                                        logEvent $ WarnUnconstrainedParameter
                                                nm VTValue
                                        return (nm, VTValue) 
                                    _ -> error $ "typeDeclarations: parameter '"
                                        ++ nm ++ "' of region type '"
                                        ++ rtname ++ "' has no type."
                        return $ Map.insert rtname pts m
                initialRDec i m v =
                        (either undefined id . bindE (RegPar i 0) VTRegionID) $ 
                        TC.declareAll [RegPar i n | n <- [0..v - 1]]
                                                m
                initialPDec i m v =
                        TC.declareAll [PredPar i n | n <- [0..v-1]]
-}

typeRegionDeclaration :: (MonadState TypingState m,
        MonadRaise m) =>
        RegionDeclr -> m ()
typeRegionDeclaration dc@(RegionDeclr sp rtname rparas gdecs sis actions) =
          contextualise dc $ do
                mapM_ (typeStateInterp resVar) sis
                mapM_ (typeAction resVar) actions
        where
                resVar s = maybe (Local s) (\x -> RegPar rtname x)
                        (elemIndex s rparas) 

typeStateInterp :: (MonadState TypingState m,
        MonadRaise m)
        => (String -> Typed)
        -> StateInterpretation
        -> m ()
typeStateInterp resVar si = do
        s <- use tsContext
        mapM_ (typePureAssrt resVar) (siConditions si)
        mapM_ (typeVarExprAs VTValue resVar) (freeL (siState si))
        typeAssrt resVar (siInterp si)
        tsContext %= (`TC.intersection` s)

typeAction :: (MonadState TypingState m, MonadRaise m)
        => (String -> Typed)
        -> Action
        -> m ()
typeAction resVar (Action _ cnds grd pre post) = do
        s <- use tsContext
        mapM_ (typePureAssrt resVar) cnds
        mapM_ (typeGuard resVar) grd
        mapM_ (typeVarExprAs VTValue resVar) $ freeL
                [pre, post]
        tsContext %= (`TC.intersection` s)


typeVarExprAs :: (MonadState TypingState m, MonadRaise m) =>
        VariableType
        -> (String -> Typed)
        -> VarExpr
        -> m ()
typeVarExprAs vt resVar ve = contextualise ve $ tve ve
        where
        tve (Variable _ v) = bindR (resVar v) vt
        tve _ = return ()

typePureAssrt :: (MonadState TypingState m, MonadRaise m)
        => (String -> Typed)
        -> PureAssrt
        -> m ()
typePureAssrt resVar = tpa
        where
                tpa (ConstBAssrt _ _) = return ()
                tpa (NotBAssrt _ pa) = tpa pa
                tpa a@(BinaryVarAssrt sp _ (Variable _ v1) (Variable _ v2)) =
                        addContext (DescriptiveContext sp $
                                "In the (dis)equality: '" ++ show a ++ "'") $
                                unifyR (resVar v1) (resVar v2)
                tpa BinaryVarAssrt{} = return ()
                tpa (BinaryValAssrt _ _ ve1 ve2) = mapM_ 
                        (typeVarExprAs VTValue resVar)
                        (freeL [ve1, ve2])
                tpa (BinaryPermAssrt _ _ pe1 pe2) = mapM_
                        (typeVarExprAs VTPermission resVar)
                        (freeL [pe1, pe2])

typeGuard :: (MonadState TypingState m, MonadRaise m)
        => (String -> Typed)
        -> Guard
        -> m ()
typeGuard resVar (NamedGuard _ _) = return ()
typeGuard resVar (PermGuard _ _ pe) = mapM_
        (typeVarExprAs VTPermission resVar) (freeL pe)
typeGuard resVar (ParamGuard _ _ args) = mapM_ (typeVarExprAs VTValue resVar) (freeL args)
typeGuard resVar (ParamSetGuard _ _ vs pas) = mapM_ (typeVarExprAs VTValue resVar) (filter notbnd $ freeL pas)
        where
          notbnd (Variable _ v) = not $ v `elem` vs
          notbnd _ = False -- might as well throw away wildcards immediately
typeGuard resVar (CountingGuard _ _ ve) = mapM_ (typeVarExprAs VTValue resVar) (freeL ve)

typeAssrt :: (MonadState TypingState m, MonadRaise m)
        => (String -> Typed)
        -> Assrt
        -> m ()
typeAssrt resVar = ta
        where
                ta (AssrtPure _ a) = typePureAssrt resVar a
                ta (AssrtSpatial _ a) = ts a
                ta (AssrtConj _ a1 a2) = ta a1 >> ta a2
                ta (AssrtITE _ ac a1 a2) = typePureAssrt resVar ac >> ta a1
                                        >> ta a2
                ta (AssrtOr _ a1 a2) = ta a1 >> ta a2
                tArg arg (AnyVar ve@(Variable _ v)) = contextualise ve $ 
                        unifyR arg (resVar v)
                tArg _ (AnyVar _) = return ()
                tArg arg (AnyVal ve) = do
                        mapM_ (typeVarExprAs VTValue resVar)
                                (freeL ve)
                        bindR arg VTValue
                tArg arg (AnyPerm pe) = do
                        mapM_ (typeVarExprAs VTPermission resVar)
                                (freeL pe)
                        bindR arg VTPermission
                ts (SARegion regass@(Region sp tname rid args st)) = do
                        decCounts <- use tsRegionTypeArities
                        contextualise regass $
                                case decCounts ^. at tname of
                                        Just c ->
                                            unless (c == length args + 1) $
                                                raise $ ArgumentCountMismatch 
                                                        (c + 1)
                                                        (length args + 2)
                                        Nothing -> raise $ UndeclaredRegionType
                                                tname (similarStrings tname 
                                                        (Map.keys decCounts))
                        addContext (DescriptiveContext sp $
                                        "In the first argument" ++
                                        " of a region assertion of type '" ++
                                        tname ++ "'") $
                            bindR (resVar rid) VTRegionID
                        iforM_ args $ \i a -> addContext
                                (DescriptiveContext sp $
                                        "In argument " ++ show (i + 2) ++
                                        " of a region assertion of type '" ++
                                        tname ++ "'") $
                                tArg (RegPar tname (i + 1)) a 
                        addContext (DescriptiveContext sp $
                                        "In the last (state) argument" ++
                                        " of a region assertion of type '" ++
                                        tname ++ "'") $
                            mapM_ (typeVarExprAs VTValue resVar)
                                (freeL st)
                ts (SAPredicate pd@(Predicate sp pname args)) = do
                        decCounts <- use tsPredicateArities
                        contextualise pd $ 
                                case decCounts ^. at pname of
                                        Just c ->
                                                unless (c == length args) $
                                                    raise $ ArgumentCountMismatch
                                                                c
                                                                (length args)
                                        Nothing -> raise $ UndeclaredPredicate
                                                pname (similarStrings pname (Map.keys decCounts))
                        iforM_ args $ \i a -> addContext
                                (DescriptiveContext sp $ "In argument " ++ show (i + 1) ++ " of a '" ++ pname ++ "' predicate assertion") $
                                        tArg (PredPar pname i) a 

                ts (SACell ca) =
                          contextualise ca $
                                mapM_ (typeVarExprAs VTValue resVar)
                                        (freeL ca)
                ts (SAGuards grds@(Guards _ _ gds)) = contextualise grds $
                        mapM_ (typeGuard resVar) gds
