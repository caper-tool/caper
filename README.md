General Installation Notes
==========================

Requirements
------------

1. The Haskell Platform; ghc versions 7.10.3 and 8.0.1 are currently supported; available from https://www.haskell.org/platform/
2. The Z3 theorem prover; version 4.4.1 or later; available from https://github.com/Z3Prover/z3/releases

Set up
------

This assumes that you are in the Caper root directory, that Z3 is at $Z3PATH and that $Z3PATH/bin is in the system path.
You may also need $Z3PATH/bin in the path to search for dynamic libraries.  On Linux:
```
  export LD_LIBRARY_PATH=$Z3PATH/bin
```
On OS X:
```
  export DYLD_LIBRARY_PATH=$Z3PATH/bin
```

First, create a cabal sandbox for Caper:
```
  cabal sandbox init
```

Next, install the dependencies:
```
  cabal update
  cabal install --dependencies-only --extra-include-dirs=$Z3PATH/include --extra-lib-dirs=$Z3PATH/bin
```
Now build Caper:
```
  cabal configure --enable-tests
  cabal build
```
Create the configuration file by copying the defaults (optionally editing):
```
  cp config.ini.default config.ini
```

Now you can run Caper:
```
  dist/build/Caper/Caper examples/recursive/SpinLock.t
```
Or the regression tests:
```
  dist/build/RunTests/RunTests
```
