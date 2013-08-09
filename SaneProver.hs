{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable, DeriveDataTypeable #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE RankNTypes #-}
module SaneProver where

import Prelude hiding (sequence,foldl,mapM_,mapM)
import qualified Data.Map as Map
import Control.Monad.State hiding (mapM_,mapM)
import Control.Monad.Trans.Maybe
import qualified Permissions as P
import Data.Maybe
import Data.Foldable
import Data.Traversable
import Data.Typeable
import Control.Monad hiding (mapM_,mapM)
--import Data.Functor.Identity


data VariableType = VTPermission
        deriving (Eq, Ord, Show)

data VariableID = VIDNamed () String
                | VIDInternal () String
                deriving (Eq,Ord,Typeable)

instance Show VariableID where
        show (VIDNamed _ s) = s
        show (VIDInternal _ s) = "__" ++ s


data EVariable = EVNormal VariableID | EVExistential () String -- | EVInternal () Int
        deriving (Eq, Ord, Typeable)

instance Show EVariable where
        show (EVNormal v) = show v
        show (EVExistential _ s) = "?" ++ s
--        show (EVInternal _ n) = "?_" ++ show n

data Literal a v = LPos (a v) | LNeg (a v) deriving (Functor, Foldable, Traversable)

instance Show (a v) => Show (Literal a v) where
        show (LPos x) = show x
        show (LNeg x) = "¬ " ++ show x

data PermissionExpression v = PEFull
                        | PEZero
                        | PEVar v
                        | PESum (PermissionExpression v) (PermissionExpression v)
                        | PECompl (PermissionExpression v)
                        deriving (Eq,Ord,Functor, Foldable, Traversable)
instance Show v => Show (PermissionExpression v) where
        show PEFull = "1"
        show PEZero = "0"
        show (PESum e1 e2) = "(" ++ show e1 ++ " + " ++ show e2 ++ ")"
        show (PECompl e) = "(1 - " ++ show e ++ ")"
        show (PEVar v) = show v

instance Monad PermissionExpression where
        return = PEVar
        (PEVar v) >>= b = b v
        PESum x y >>= b = PESum (x >>= b) (y >>= b)
        PECompl e >>= b = PECompl (e >>= b)
        PEFull >>= _ = PEFull
        PEZero >>= _ = PEZero

data PermissionAtomic v =
                 PAEq (PermissionExpression v) (PermissionExpression v)
                | PADis (PermissionExpression v) (PermissionExpression v)
                deriving (Functor, Foldable, Traversable)

class PermExprSubable c where
        permExprSub :: (v -> PermissionExpression w) -> c v -> c w

instance PermExprSubable PermissionExpression where
        permExprSub a b = b >>= a

instance PermExprSubable PermissionAtomic where
        permExprSub s (PAEq x y) = PAEq (permExprSub s x) (permExprSub s y)
        permExprSub s (PADis x y) = PADis (permExprSub s x) (permExprSub s y)

instance Show v => Show (PermissionAtomic v) where
        show (PAEq v1 v2) = show v1 ++ " =p= " ++ show v2
        show (PADis v1 v2) = show v1 ++ " # " ++ show v2

type VIDPermissionAtomic = PermissionAtomic VariableID

type PermissionLiteral = Literal PermissionAtomic

instance PermExprSubable (Literal PermissionAtomic) where
        permExprSub s (LPos a) = LPos (permExprSub s a)
        permExprSub s (LNeg a) = LNeg (permExprSub s a)


data Assertion = PermissionAssertion (Literal PermissionAtomic VariableID)

instance Show Assertion where
        show (PermissionAssertion pa) = show pa

data Context = Context {
        bindings :: Map.Map VariableID VariableType,
        assertions :: [Assertion]
        }

type ProverT = StateT Context

type Prover = State Context


instance Show Context where
        show (Context _ as) = foldl (++) "" $ map (('\n':) . show) as

emptyContext :: Context
-- A context with no variables and no assertions
emptyContext = Context Map.empty []

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

type DPF = P.PermFormula


pXvar :: (Ord v, Monad m) => (DPF->DPF) -> v -> StateT (Int, Map.Map v Int, DPF -> DPF) m ()
pXvar x vid = do
                (n, m, c) <- get
                case Map.lookup vid m of
                        (Just _) -> return ()
                        Nothing -> do
                                put (n+1, Map.insert vid (n+1) m, c . x)
                                return ()

pgetVar :: (Ord v, Monad m) => v -> StateT (Int, Map.Map v Int, DPF -> DPF) m Int
pgetVar vid = do
                (n, m, c) <- get
                let k = Map.findWithDefault (error "Internal error: pgetVar called on uninitialised variable") vid m
                return $ n - k

pXvars x vids = mapM_ (pXvar x) vids >> mapM pgetVar vids

pavars :: (Ord v, Monad m) => [v] -> StateT (Int, Map.Map v Int, DPF -> DPF) m [Int]
pavars = pXvars P.PFAll

pevars :: (Ord v, Monad m) => [v] -> StateT (Int, Map.Map v Int, DPF -> DPF) m [Int]
pevars = pXvars P.PFEx

pXvars_ :: (Ord v, Traversable f, Monad m) => (DPF -> DPF) -> f v -> StateT (Int, Map.Map v Int, DPF -> DPF) m ()
pXvars_ x = mapM_ (pXvar x)
pavars_ :: (Ord v, Traversable f, Monad m) => f v -> StateT (Int, Map.Map v Int, DPF -> DPF) m ()
pavars_ = pXvars_ P.PFAll
pevars_ :: (Ord v, Traversable f, Monad m) => f v -> StateT (Int, Map.Map v Int, DPF -> DPF) m ()
pevars_ = pXvars_ P.PFEx

mapSecond :: (b -> b) -> (a, b, c) -> (a, b, c)
mapSecond f (x,y,z) = (x, f y, z)

mapThird :: (c -> c) -> (a, b, c) -> (a, b, c)
mapThird f (x, y, z) = (x, y, f z)


deBrujinify :: (Functor k, Ord v) => Map.Map v Int -> k v -> k Int
deBrujinify m = fmap (\x -> Map.findWithDefault (error "Internal error: deBrujinify used on uninitialised variable") x m)

toPermExpr :: PermissionExpression Int -> P.PermExpr
toPermExpr PEFull = P.PEFull
toPermExpr PEZero = P.PEZero
toPermExpr (PEVar n) = P.PEVar n
toPermExpr (PESum e1 e2) = P.PESum (toPermExpr e1) (toPermExpr e2)
toPermExpr (PECompl e) = P.PECompl (toPermExpr e)

toPermAtom :: PermissionAtomic Int -> P.PermAtom
toPermAtom (PAEq e1 e2) = P.PAEqual (toPermExpr e1) (toPermExpr e2)
toPermAtom (PADis e1 e2) = P.PADisjoint (toPermExpr e1) (toPermExpr e2)

-- Got to think of better names for these!
pass :: Monad m => VIDPermissionAtomic -> (DPF -> DPF) -> StateT (Int, Map.Map VariableID Int, DPF -> DPF) m ()
pass f m = do
                pavars_ f
                (_, s, _) <- get
                modify $ mapThird (. (P.PFImpl $ m $ P.PFAtom $ toPermAtom $ deBrujinify s f))

passt :: Monad m => PermissionLiteral VariableID -> StateT (Int, Map.Map VariableID Int, DPF -> DPF) m ()
passt (LPos x) = pass x id
passt (LNeg x) = pass x P.PFNot

passtl :: Monad m => [PermissionLiteral VariableID] -> StateT (Int, Map.Map VariableID Int, DPF -> DPF) m ()
passtl = mapM_ passt
--passtl [] = return ()
--passtl (l:ls) = passt l >> passtl ls

permissionConsistentDPF :: [PermissionLiteral VariableID] -> DPF
permissionConsistentDPF ls = let (_, (_, _, x)) = runState (passtl ls) (0, Map.empty, id) in P.PFNot $ x P.PFFalse


type PermissionEConsequences = [Literal PermissionAtomic EVariable]

filterPermissionAssertions :: Context -> [PermissionLiteral VariableID]
filterPermissionAssertions = mapMaybe getperms . assertions
        where
                getperms (PermissionAssertion a) = Just a
--                getperms _ = Nothing



-- Got to think of better names for these!
pechk :: (Ord v, Monad m) => PermissionAtomic v -> (DPF -> DPF) -> StateT (Int, Map.Map v Int, DPF -> DPF) m ()
pechk f m = do
                pevars_ f
                (_, s, _) <- get
                modify $ mapThird (. (P.PFAnd $ m $ P.PFAtom $ toPermAtom $ deBrujinify s f))

pechkt :: (Ord v, Monad m) => Literal PermissionAtomic v -> StateT (Int, Map.Map v Int, DPF -> DPF) m ()
pechkt (LPos x) = pechk x id
pechkt (LNeg x) = pechk x P.PFNot

pechktl :: (Ord v, Monad m) => [Literal PermissionAtomic v] -> StateT (Int, Map.Map v Int, DPF -> DPF) m ()
pechktl = mapM_ pechkt

allPermissionVars :: Context -> [VariableID]
allPermissionVars = Map.foldWithKey permissionVarFold [] . bindings
        where
                permissionVarFold vid t = if t == VTPermission then (vid:) else id

permCheckEConsequences :: Context -> PermissionEConsequences -> DPF
permCheckEConsequences c ecs = let (_, (n, m, x)) = runState (passtl (filterPermissionAssertions c) >> pavars (allPermissionVars c)) (0, Map.empty, id) in
                        let m' = Map.mapKeys EVNormal m in
                        let (_, (_, _, r)) = runState (pechktl ecs) (n, m', x) in r P.PFTrue

permDoCheckEConsequences :: (Monad m, MonadPlus m) => PermissionEConsequences -> ProverT m ()
permDoCheckEConsequences pecs = do
                                c <- get
                                let r = P.pf_eval $ permCheckEConsequences c pecs
                                if r then return () else mzero



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
                        let pl' = permExprSub id pl
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

check :: MonadPlus m => CheckerT m a -> ProverT m (a, EvarSubstitution)
-- Check whether the assertions hold.
-- If so, grant them, if not fail this path
check c = do
        (r, (pecs, subs)) <- runStateT c ([], Map.empty)
        let pecs' = map (permExprSub (liftSubs subs)) pecs
        permDoCheckEConsequences pecs'
        subs' <- permAssertEConsequences pecs' (Map.mapMaybe id subs)
        return (r, evarSubs subs')
        where
                liftSubs :: Map.Map String (Maybe (PermissionExpression VariableID)) -> EVariable -> PermissionExpression EVariable
                liftSubs s x@(EVExistential _ e) = case Map.lookup e s of
                        Nothing -> PEVar x
                        (Just Nothing) -> PEVar x
                        (Just (Just pe)) -> fmap EVNormal pe
                evarSubs :: Map.Map String (PermissionExpression VariableID) -> EvarSubstitution
                evarSubs s (EVNormal vid) = Just $ PEVar vid
                evarSubs s (EVExistential _ n) = Map.lookup n s

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
