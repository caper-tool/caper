{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable, DeriveDataTypeable #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE RankNTypes #-}
module SaneProver where

import Prelude hiding (sequence,foldl,mapM_,mapM,elem,notElem)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Control.Monad.State hiding (mapM_,mapM)
import Control.Monad.Trans.Maybe
import PermissionsInterface
import Permissions
import Data.Maybe
import Data.Foldable
import Data.Traversable
import Data.Typeable
import Control.Monad hiding (mapM_,mapM)
import ProverDatatypes
--import Data.Functor.Identity



freshVariable :: Context -> String -> VariableID
-- Return a variable identifier not currently bound in the context
freshVariable c s = head $ filter (\x -> Map.notMember x (bindings c))
                        [ VIDInternal () $ s ++ n | n <- "" : map show [0..] ]

freshPermission :: Monad m => String -> ProverT m VariableID
-- Bind a fresh permission variable
freshPermission s = do
                        c <- get
                        let vid = freshVariable c s
                        put $ c { bindings = Map.insert vid VTPermission (bindings c) }
                        return vid

checkBindVariable :: Monad m => () -> String -> VariableType -> ProverT m VariableID
-- Check if the named variable is bound
-- If it is, its current type must be consistent with the proposed type
-- If not, then a new binding is created
checkBindVariable meta name vartype = let vid = VIDNamed meta name in do
                c <- get
                case Map.lookup vid (bindings c) of
                        (Just t) -> if t == vartype then return vid else fail ("Variable \"" ++ name ++ "\" is used with type " ++ show vartype ++ " when its expected type is " ++ show t ++ ".")
                        Nothing -> do
                                put $ c { bindings = Map.insert vid vartype (bindings c) }
                                return vid


assert :: Monad m => Assertion -> ProverT m ()
-- Add an assertion
assert a = do
                c <- get
                put $ c { assertions = assertions c ++ [a] }

assertPermissionTrue :: Monad m => VIDPermissionAtomic -> ProverT m ()
-- Assert a permission atomic to be true
assertPermissionTrue = assert . PermissionAssertion . LPos

assertPermissionFalse :: Monad m => VIDPermissionAtomic -> ProverT m ()
-- Assert a permission atomic to be false
assertPermissionFalse = assert . PermissionAssertion . LNeg

-- checkConsistent :: State Context Bool
-- Returns true if the current assertions are consistent

type PermissionEConsequences = [Literal PermissionAtomic EVariable]

filterPermissionAssertions :: Context -> [PermissionLiteral VariableID]
filterPermissionAssertions = mapMaybe getperms . assertions
        where
                getperms (PermissionAssertion a) = Just a
--                getperms _ = Nothing


type PermFOF = FOF PermissionAtomic String

vidToString :: VariableID -> String
vidToString (VIDNamed _ n) = "n_" ++ n
vidToString (VIDInternal _ n) = "i_" ++ n

evarToString :: EVariable -> String
evarToString (EVExistential _ n) = "e_" ++ n
evarToString (EVNormal v) = vidToString v

contextToPermFOF :: Context -> PermFOF -> PermFOF
-- Generate a first-order formula from a context, and a first-order formula to check inside the context
contextToPermFOF c@(Context bs as) = cPFOF (Map.mapMaybe (\x -> if x == VTPermission then Just False else Nothing) bs) (filterPermissionAssertions c)
        where
                cPFOF :: Map.Map VariableID Bool -> [PermissionLiteral VariableID] -> PermFOF -> PermFOF
                cPFOF bs [] r = Map.foldrWithKey (\v bound -> if bound || notElem (vidToString v) r then id else FOFForAll (vidToString v)) r bs
                cPFOF bs (a : as) r = let (bdgs, bs') = runState (foldrM checkBind id a) bs in (bdgs . (FOFImpl $ literalToFOF (fmap vidToString a)) . (cPFOF bs' as)) r
                checkBind v bds = do
                                bv <- gets (Map.lookup v)
                                if bv == Just True then return bds else do
                                        modify (Map.insert v True)
                                        return $ (FOFForAll (vidToString v)) . bds
                        
eConsequencesToPermFOF :: PermissionEConsequences -> PermFOF
-- Generate a first-order formula as the conjunction of the PermissionEConsequences, with all existential vars scoped.
eConsequencesToPermFOF = eCPFOF Set.empty
        where
                eCPFOF :: Set.Set String -> PermissionEConsequences -> PermFOF
                eCPFOF _ [] = FOFTrue
                eCPFOF s (c : cs) = let (bdgs, s') = runState (foldrM checkBind id c) s in bdgs $ FOFAnd (literalToFOF (fmap evarToString c)) (eCPFOF s' cs)
                checkBind (EVNormal _) bds = return bds
                checkBind ex@(EVExistential _ e) bds = do
                                bv <- gets (elem e)
                                if bv then return bds else do
                                        modify (Set.insert e)
                                        return $ (FOFExists (evarToString ex)) . bds
                        

permCheckEConsequences :: Context -> PermissionEConsequences -> PermFOF
permCheckEConsequences c pecs = contextToPermFOF c $ eConsequencesToPermFOF pecs

permDoCheckEConsequences :: (MonadIO m, MonadPlus m, PermissionsProver p) => p -> PermissionEConsequences -> ProverT m ()
permDoCheckEConsequences prover pecs = do
                                c <- get
                                r <- liftIO $ permCheckTrue prover $ permCheckEConsequences c pecs
                                if r then return () else
                                        fail $ "Unsatisfiable constraints:\n" ++ show pecs ++ "\n in context:" ++ show c


instantiateEvar :: Monad m => EVariable -> StateT (Map.Map String (PermissionExpression VariableID)) (ProverT m) (PermissionExpression VariableID)
instantiateEvar (EVNormal vid) = return $ PEVar vid -- TODO: check that the variable is bound/bind it if not?
instantiateEvar (EVExistential () name) = do
                                        mv <- gets (Map.lookup name)
                                        case mv of
                                                (Just vid) -> return vid
                                                Nothing -> do
                                                        vid <- lift $ freshPermission name
                                                        modify $ Map.insert name (PEVar vid)
                                                        return (PEVar vid)

permAssertEConsequences :: Monad m => PermissionEConsequences -> Map.Map String (PermissionExpression VariableID)
                                -> ProverT m (Map.Map String (PermissionExpression VariableID))
-- Update the context by asserting properties of permissions, possibly including evars
-- The evars become instantiated as fresh internal variables
-- The returned Map defines the substitution for evars
permAssertEConsequences ecs mp = liftM snd $ runStateT (mapM paec ecs) mp
        where
                paec :: Monad m => Literal PermissionAtomic EVariable ->
                        StateT (Map.Map String (PermissionExpression VariableID)) (ProverT m) ()
                paec ec = do
                        pl <- mapM instantiateEvar ec
                        let pl' = exprSub id pl
                        lift $ assert (PermissionAssertion pl')


mapProver :: (forall s. m (a, s) -> n (b, s)) -> ProverT m a -> ProverT n b
mapProver x = mapStateT x

-- Remark: This is currently only set for permissions.  Will need to make it work more generally.

type CheckerT m = StateT (PermissionEConsequences, Map.Map String (Maybe (PermissionExpression VariableID))) (ProverT m)

type EvarSubstitution = EVariable -> Maybe (PermissionExpression VariableID)

bindEvar :: Monad m => String -> PermissionExpression VariableID -> CheckerT m ()
-- Binds an evar to a permission expression (in existing variables)
-- If there already is a binding, this generates a condition that
-- the bound expressions be equal
bindEvar name expr = do
                (ecs, subs) <- get
                case Map.lookup name subs of
                        Nothing -> put (ecs, Map.insert name (Just expr) subs)
                        (Just Nothing) -> put (ecs, Map.insert name (Just expr) subs)
                        (Just (Just x)) -> if x == expr then return () else put (ecs ++ [fmap EVNormal $ LPos $ PAEq expr x], subs)

freshEvar :: Monad m => CheckerT m String
-- Returns a fresh evar
freshEvar = do
                c <- lift get
                (ecs, s) <- get
                let ev = head $ filter (\x -> Map.notMember (VIDInternal () x) (bindings c) && Map.notMember x s)
                        [ "_evar" ++ n | n <- map show [0..] ]
                put (ecs, Map.insert ev Nothing s)
                return ev
                
addConstraint :: MonadPlus m => Literal PermissionAtomic EVariable -> CheckerT m ()
addConstraint l = do -- Possibly check bindings for evars. Probably only an issue if evars called _evar[0-9]* are not generated by freshEvar
                (ecs, s) <- get
                put (l : ecs, s)

checkWith :: (MonadIO m, MonadPlus m, PermissionsProver p) => p -> CheckerT m a -> ProverT m (a, EvarSubstitution)
-- Check whether the assertions hold.
-- If so, grant them, if not fail this path
checkWith prover c = do
        (r, (pecs, subs)) <- runStateT c ([], Map.empty)
        let pecs' = map (exprSub (liftSubs subs)) pecs
        permDoCheckEConsequences prover pecs'
        subs' <- permAssertEConsequences pecs' (Map.mapMaybe id subs)
        return (r, evarSubs subs')
        where
                liftSubs :: Map.Map String (Maybe (PermissionExpression VariableID)) -> EVariable -> PermissionExpression EVariable
                liftSubs s x@(EVExistential _ e) = case Map.lookup e s of
                        Nothing -> PEVar x
                        (Just Nothing) -> PEVar x
                        (Just (Just pe)) -> fmap EVNormal pe
                liftSubs _ x@(EVNormal _) = PEVar x
                evarSubs :: Map.Map String (PermissionExpression VariableID) -> EvarSubstitution
                evarSubs s (EVNormal vid) = Just $ PEVar vid
                evarSubs s (EVExistential _ n) = Map.lookup n s

check :: (MonadIO m, MonadPlus m) => CheckerT m a -> ProverT m (a, EvarSubstitution)
check = checkWith (TPProver ())

{--

var_foo = VIDNamed () "foo"
var_x = VIDNamed () "x"
var_y = VIDNamed () "y"
pllist1 = [
        LNeg $ PAEq (PEVar var_x) PEZero,
        LPos $ PAEq (PEVar var_foo) PEZero,
        LPos $ PAEq (PESum (PEVar var_x) (PEVar var_y)) (PEVar var_foo)]
pllist1b = [LPos $ PAEq (PESum (PEVar var_x) (PEVar var_y)) (PEVar var_foo),
        LNeg $ PAEq (PEVar var_x) PEZero,
        LPos $ PAEq (PEVar var_foo) PEZero
        ]
pllist2 = [LPos $ PAEq (PESum (PEVar var_x) (PEVar var_y)) (PEVar var_foo),
        LNeg $ PAEq (PEVar var_x) PEZero,
        LPos $ PAEq (PEVar var_y) PEZero,
        LPos $ PAEq (PEVar var_foo) PEFull
        ]


c0 = snd $ runState x emptyContext
        where
                x = do
                        foo <- checkBindVariable () "foo" VTPermission
                        assertPermissionFalse $ PAEq (PEVar foo) PEZero
                        x <- checkBindVariable () "x" VTPermission
                        y <- checkBindVariable () "y" VTPermission
                        assertPermissionTrue $ PAEq (PESum (PEVar x) (PEVar y)) (PEVar foo)
                        return ()
--
evar_bar = EVExistential () "bar"

ec = [
--        LPos $ PATotalFull [EVNormal var_foo, evar_bar],
        LPos $ PADis (EVNormal var_x) evar_bar,
        LPos $ PADis evar_bar (EVNormal var_y),
        LNeg $ PADis (EVNormal var_foo) evar_bar
        ]

c1 = snd $ runState x emptyContext
        where
                x = do
                        foo <- checkBindVariable () "foo" VTPermission
                        return ()

ec1 = [ LPos $ PAFull var_foo ]
 --}
