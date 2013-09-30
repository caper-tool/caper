import PermissionsInterface
import ProverDatatypes
import Permissions
import PermissionsE

fpf1 = FOFExists "v" $ FOFForAll "w" $ FOFAtom $ PADis (PEVar "v") (PEVar "w")
fpf2 = FOFExists "v" $ FOFForAll "w" $ FOFImpl (FOFForAll "u" $ FOFAtom $ PADis (PEVar "u") (PEVar "w")) (FOFAtom $ PAEq (PEVar "v") (PEVar "w"))
fpf4 = FOFForAll "x" $ FOFImpl (FOFForAll "y" $ FOFOr (FOFAtom $ PAEq (PEVar "y") PEZero) (FOFNot $ FOFAtom $ PADis (PEVar "y") (PEVar "x"))) $ FOFForAll "a" $ FOFForAll "b" $ FOFForAll "c" $ FOFForAll "d" $ FOFImpl (FOFAtom $ PAEq (PESum (PEVar "d") (PEVar "c")) (PEVar "x")) $ FOFImpl (FOFAtom $ PAEq (PESum (PEVar "b") (PEVar "a")) (PEVar "x")) $ FOFImpl (FOFAtom $ PAEq (PEVar "b") (PEVar "d")) (FOFAtom $ PAEq (PEVar "a") (PEVar "c"))
fpf5 = FOFForAll "x" $ FOFOr (FOFAtom $ PADis (PEVar "x") (PEVar "x")) (FOFExists "y" $ FOFExists "z" $ FOFAnd (FOFAnd (FOFNot $ FOFAtom $ PADis (PEVar "z") (PEVar "z")) (FOFNot $ FOFAtom $ PADis (PEVar "y") (PEVar "y"))) (FOFAtom $ PAEq (PESum (PEVar "z") (PEVar "y")) (PEVar "x"))) 
provers = do
	prel <- tptpBAPrelude
	return (TPProver (), EPProver prel "c:\\cygwin64\\home\\Thomas\\E\\PROVER\\eprover.exe")
