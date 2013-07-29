{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# LANGUAGE FlexibleContexts #-}
module SaneProver where

import Prelude hiding (mapM,sequence,foldl,mapM_,mapM)
import qualified Data.Map as Map
import Control.Monad.State hiding (mapM_,mapM)
import Permissions
import Data.Maybe
import Data.Foldable
import Data.Traversable

data VariableType = VTPermission
        deriving (Eq, Ord, Show)

data VariableID = VIDNamed () String
                | VIDInternal () String
                deriving (Eq,Ord)

instance Show VariableID where
        show (VIDNamed _ s) = s
        show (VIDInternal _ s) = "__" ++ s


data EVariable = EVNormal VariableID | EVExistential () String
        deriving (Eq, Ord)

instance Show EVariable where
        show (EVNormal v) = show v
        show (EVExistential _ s) = "?" ++ s

data Literal a v = LPos (a v) | LNeg (a v) deriving (Functor, Foldable, Traversable)

instance Show (a v) => Show (Literal a v) where
        show (LPos x) = show x
        show (LNeg x) = "¬ " ++ show x

data PermissionAtomic v = PAZero v
                | PAFull v
                | PAComp v v v
                | PAEq v v
                | PADis v v
                | PATotalFull [v]
                deriving (Functor, Foldable, Traversable)

instance Show v => Show (PermissionAtomic v) where
        show (PAZero v) = "0 =p= " ++ show v
        show (PAFull v) = "1 =p= " ++ show v
        show (PAComp v1 v2 v3) = show v1 ++ " + " ++ show v2 ++ " =p= " ++ show v3
        show (PAEq v1 v2) = show v1 ++ " =p= " ++ show v2
        show (PADis v1 v2) = show v1 ++ " # " ++ show v2
        show (PATotalFull vs) = "1/undef =p= " ++ foldl (\x y -> x ++ " + " ++ y) "0" (map show vs)

type VIDPermissionAtomic = PermissionAtomic VariableID

type PermissionLiteral = Literal PermissionAtomic


data Assertion = PermissionAssertion (Literal PermissionAtomic VariableID)

instance Show Assertion where
        show (PermissionAssertion pa) = show pa

data Context = Context {
        bindings :: Map.Map VariableID VariableType,
        assertions :: [Assertion]
        }

instance Show Context where
        show (Context _ as) = foldl (++) "" $ map ('\n':) $ map show as

emptyContext :: Context
-- A context with no variables and no assertions
emptyContext = Context Map.empty []

freshVariable :: Context -> String -> VariableID
-- Return a variable identifier not currently bound in the context
freshVariable c s = head $ filter (\x -> Map.notMember x (bindings c))
                        [ VIDInternal () $ s ++ n | n <- "" : map show [0..] ]

freshPermission :: String -> State Context VariableID
-- Bind a fresh permission variable
freshPermission s = do
                        c <- get
                        let vid = freshVariable c s
                        put $ (c { bindings = Map.insert vid VTPermission (bindings c) })
                        return vid

checkBindVariable :: () -> String -> VariableType -> State Context VariableID
-- Check if the named variable is bound
-- If it is, its current type must be consistent with the proposed type
-- If not, then a new binding is created
checkBindVariable meta name vartype = let vid = VIDNamed meta name in do
                c <- get
                case Map.lookup vid (bindings c) of
                        (Just t) -> if t == vartype then return vid else fail ("Variable \"" ++ name ++ "\" is used with type " ++ (show vartype) ++ " when its expected type is " ++ (show t) ++ ".")
                        Nothing -> do
                                put $ c { bindings = Map.insert vid vartype (bindings c) }
                                return vid


assert :: Assertion -> State Context ()
-- Add an assertion
assert a = do
                c <- get
                put $ c { assertions = assertions c ++ [a] }

assertPermissionTrue :: VIDPermissionAtomic -> State Context ()
-- Assert a permission atomic to be true
assertPermissionTrue = assert . PermissionAssertion . LPos

assertPermissionFalse :: VIDPermissionAtomic -> State Context ()
-- Assert a permission atomic to be false
assertPermissionFalse = assert . PermissionAssertion . LNeg

-- checkConsistent :: State Context Bool
-- Returns true if the current assertions are consistent


pXvar :: Ord v => (DPF->DPF) -> v -> State (Int, Map.Map v Int, DPF -> DPF) ()
pXvar x vid = do
                (n, m, c) <- get
                case Map.lookup vid m of
                        (Just _) -> return ()
                        Nothing -> do
                                put $ (n+1, Map.insert vid (n+1) m, c . x)
                                return ()

pgetVar :: Ord v => v -> State (Int, Map.Map v Int, DPF -> DPF) Int
pgetVar vid = do
                (n, m, c) <- get
                let k = Map.findWithDefault (error "Internal error: pgetVar called on uninitialised variable") vid m
                return $ n - k

pXvars x vids = mapM_ (pXvar x) vids >> mapM pgetVar vids

pavars :: Ord v => [v] -> State (Int, Map.Map v Int, DPF -> DPF) [Int]
pavars = pXvars DAll

pevars :: Ord v => [v] -> State (Int, Map.Map v Int, DPF -> DPF) [Int]
pevars = pXvars DEx


mapSecond :: (b -> b) -> (a, b, c) -> (a, b, c)
mapSecond f (x,y,z) = (x, f y, z)

mapThird :: (c -> c) -> (a, b, c) -> (a, b, c)
mapThird f (x, y, z) = (x, y, f z)

-- Got to think of better names for these!
pass :: VIDPermissionAtomic -> (DPF -> DPF) -> State (Int, Map.Map VariableID Int, DPF -> DPF) ()
pass (PAZero vid) m = do
                        [k] <- pavars [vid]
                        modify $ mapThird (. (dImpl $ m $ DZero k))
pass (PAFull vid) m = do
                        [k] <- pavars [vid]
                        modify $ mapThird (. (dImpl $ m $ DFull k))
pass (PAComp v1 v2 v3) m = do
                        [k1,k2,k3] <- pavars [v1,v2,v3]
                        modify $ mapThird (. (dImpl $ m $ DC k1 k2 k3))
pass (PAEq v1 v2 ) m = do
                        [k1,k2] <- pavars [v1,v2]
                        modify $ mapThird (. (dImpl $ m $ DEq k1 k2))
pass (PADis v1 v2) m = do
                        [k1,k2] <- pavars [v1,v2]
                        modify $ mapThird (. (dImpl $ m $ DDis k1 k2))
pass (PATotalFull vs) m = do
                        ks <- pavars vs
                        modify $ mapThird (. (dImpl $ m $ DTotalFull ks))

passt :: PermissionLiteral VariableID -> State (Int, Map.Map VariableID Int, DPF -> DPF) ()
passt (LPos x) = pass x id
passt (LNeg x) = pass x DNot

passtl :: [PermissionLiteral VariableID] -> State (Int, Map.Map VariableID Int, DPF -> DPF) ()
passtl [] = return ()
passtl (l:ls) = passt l >> passtl ls

permissionConsistentDPF :: [PermissionLiteral VariableID] -> DPF
permissionConsistentDPF ls = let (_, (_, _, x)) = runState (passtl ls) (0, Map.empty, id) in DNot $ x DFalse


type PermissionEConsequences = [Literal PermissionAtomic EVariable]

filterPermissionAssertions :: Context -> [PermissionLiteral VariableID]
filterPermissionAssertions = (mapMaybe getperms) . assertions
        where
                getperms (PermissionAssertion a) = Just a
--                getperms _ = Nothing



-- Think harder.  We should introduce the remaining universal variables first.
-- Naieve approach: use the context, you idiot!



-- Got to think of better names for these!
pechk :: Ord v => PermissionAtomic v -> (DPF -> DPF) -> State (Int, Map.Map v Int, DPF -> DPF) ()
pechk (PAZero vid) m = do
                        [k] <- pevars [vid]
                        modify $ mapThird (. (DAnd $ m $ DZero k))
pechk (PAFull vid) m = do
                        [k] <- pevars [vid]
                        modify $ mapThird (. (DAnd $ m $ DFull k))
pechk (PAComp v1 v2 v3) m = do
                        [k1,k2,k3] <- pevars [v1,v2,v3]
                        modify $ mapThird (. (DAnd $ m $ DC k1 k2 k3))
pechk (PAEq v1 v2 ) m = do
                        [k1,k2] <- pevars [v1,v2]
                        modify $ mapThird (. (DAnd $ m $ DEq k1 k2))
pechk (PADis v1 v2) m = do
                        [k1,k2] <- pevars [v1,v2]
                        modify $ mapThird (. (DAnd $ m $ DDis k1 k2))
pechk (PATotalFull vs) m = do
                        ks <- pevars vs
                        modify $ mapThird (. (DAnd $ m $ DTotalFull ks))

pechkt :: Ord v => Literal PermissionAtomic v -> State (Int, Map.Map v Int, DPF -> DPF) ()
pechkt (LPos x) = pechk x id
pechkt (LNeg x) = pechk x DNot

pechktl :: Ord v => [Literal PermissionAtomic v] -> State (Int, Map.Map v Int, DPF -> DPF) ()
pechktl [] = return ()
pechktl (l:ls) = pechkt l >> pechktl ls

allPermissionVars :: Context -> [VariableID]
allPermissionVars = Map.foldWithKey permissionVarFold [] . bindings
        where
                permissionVarFold vid t = if t == VTPermission then (vid:) else id

permCheckEConsequences :: Context -> PermissionEConsequences -> DPF
permCheckEConsequences c ecs = let (_, (n, m, x)) = runState ((passtl $ filterPermissionAssertions c) >> pavars (allPermissionVars c)) (0, Map.empty, id) in
                        let m' = Map.mapKeys EVNormal m in
                        let (_, (_, _, r)) = runState (pechktl ecs) (n, m', x) in (r (DNot DFalse))



instantiateEvar :: EVariable -> StateT (Map.Map String VariableID) (State Context) VariableID
instantiateEvar (EVNormal vid) = return vid -- TODO: check that the variable is bound/bind it if not?
instantiateEvar (EVExistential () name) = do
                                        mv <- gets (Map.lookup name)
                                        case mv of
                                                (Just vid) -> return vid
                                                Nothing -> do
                                                        vid <- lift $ freshPermission name
                                                        modify $ Map.insert name vid
                                                        return vid


permAssertEConsequences :: PermissionEConsequences -> State Context (Map.Map String VariableID)
-- Update the context by asserting properties of permissions, possibly including evars
-- The evars become instantiated as fresh internal variables
-- The returned Map defines the substitution for evars
permAssertEConsequences ecs = runStateT (mapM paec ecs) Map.empty >>= return . snd
        where
                paec :: Literal PermissionAtomic EVariable ->
                        StateT (Map.Map String VariableID) (State Context) ()
                paec ec = do
                        pl <- mapM instantiateEvar ec
                        lift $ assert (PermissionAssertion pl)




var_foo = VIDNamed () "foo"
var_x = VIDNamed () "x"
var_y = VIDNamed () "y"

pllist1 = [
        LNeg $ PAZero var_x,
        LPos $ PAZero var_foo,
        LPos $ PAComp var_x var_y var_foo]
pllist1b = [LPos $ PAComp var_x var_y var_foo,
        LNeg $ PAZero var_x,
        LPos $ PAZero var_foo
        ]
pllist2 = [LPos $ PAComp var_x var_y var_foo,
        LNeg $ PAZero var_x,
        LPos $ PAZero var_y,
        LPos $ PAFull var_foo
        ]


c0 = snd $ runState x emptyContext
        where
                x = do
                        foo <- checkBindVariable () "foo" VTPermission
                        assertPermissionFalse $ PAZero foo
                        x <- checkBindVariable () "x" VTPermission
                        y <- checkBindVariable () "y" VTPermission
                        assertPermissionTrue $ PAComp x y foo
                        return ()

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
