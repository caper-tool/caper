--import PermissionsInterface
import Caper.ProverDatatypes
import Caper.PermissionsI
import Caper.PermissionsSMT
--import PermissionsE

fpf1 = FOFExists "v" $ FOFForAll "w" $ FOFAtom $ PADis (PEVar "v") (PEVar "w")
fpf2 = FOFExists "v" $ FOFForAll "w" $ FOFImpl (FOFForAll "u" $ FOFAtom $ PADis (PEVar "u") (PEVar "w")) (FOFAtom $ PAEq (PEVar "v") (PEVar "w"))
fpf4 = FOFForAll "x" $ FOFImpl (FOFForAll "y" $ FOFOr (FOFAtom $ PAEq (PEVar "y") PEZero) (FOFNot $ FOFAtom $ PADis (PEVar "y") (PEVar "x"))) $ FOFForAll "a" $ FOFForAll "b" $ FOFForAll "c" $ FOFForAll "d" $ FOFImpl (FOFAtom $ PAEq (PESum (PEVar "d") (PEVar "c")) (PEVar "x")) $ FOFImpl (FOFAtom $ PAEq (PESum (PEVar "b") (PEVar "a")) (PEVar "x")) $ FOFImpl (FOFAtom $ PAEq (PEVar "b") (PEVar "d")) (FOFAtom $ PAEq (PEVar "a") (PEVar "c"))
fpf5 = FOFForAll "x" $ FOFOr (FOFAtom $ PADis (PEVar "x") (PEVar "x")) (FOFExists "y" $ FOFExists "z" $ FOFAnd (FOFAnd (FOFNot $ FOFAtom $ PADis (PEVar "z") (PEVar "z")) (FOFNot $ FOFAtom $ PADis (PEVar "y") (PEVar "y"))) (FOFAtom $ PAEq (PESum (PEVar "z") (PEVar "y")) (PEVar "x"))) 
-- Cross split
fpf6 = FOFForAll "a" $ FOFForAll "b" $ FOFForAll "c" $ FOFForAll "d" $
        FOFImpl (FOFAtom $ PAEq (PESum (PEVar "a") (PEVar "b")) (PESum (PEVar "c") (PEVar "d"))) $
            FOFExists "ac" $ FOFExists "ad" $ FOFExists "bc" $ FOFExists "bd" $
            FOFAnd
                (FOFAnd (FOFAtom $ PAEq (PEVar "a") (PESum (PEVar "ac") (PEVar "ad")))
                        (FOFAtom $ PAEq (PEVar "b") (PESum (PEVar "bc") (PEVar "bd"))))
                (FOFAnd (FOFAtom $ PAEq (PEVar "c") (PESum (PEVar "ac") (PEVar "bc")))
                        (FOFAtom $ PAEq (PEVar "d") (PESum (PEVar "ad") (PEVar "bd"))))
{--
provers = do
	prel <- tptpBAPrelude
	return (TPProver (), EPProver prel "c:\\cygwin64\\home\\Thomas\\E\\PROVER\\eprover.exe")
--}
{--
main = mapM_ doit [1000..1010]
    where
      doit n = do
        let f = softEq n
        r <- permCheckBigInt f
        --print f
        print r
--}
main = permCheckBigInt fpf6 >>= print

deepEq n = de ["x" ++ show k | k <- [1..n]]
        where
                de l = alls l $ eqs l $ meq (head l) (last l)
                meq x y = FOFAtom $ PAEq (PEVar x) (PEVar y)
                alls [] = id
                alls (x : xs) = (alls xs) . (FOFForAll x)
                eqs (x : y : zs) = (eqs (y : zs)) . (FOFImpl (meq x y))
                eqs _ = id

softEq n = se ["x" ++ show k | k <- [1..n]]
        where
                se l = FOFForAll (last l) $ eqs l $ meq (head l) (last l)
                meq x y = FOFAtom $ PAEq (PEVar x) (PEVar y)
                eqs (x : y : zs) = (eqs (y : zs)) . (FOFForAll x) . (FOFImpl (meq x y))
                eqs _ = id
