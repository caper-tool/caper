// Compare-and-swap lock

region CASLock(r,x) {
  guards %LOCK * UNLOCK;
  interpretation {
    0 : x |-> 0 &*& r@(UNLOCK);
    1 : x |-> 1;
  }
  actions {
    LOCK[_] : 0 ~> 1;
    UNLOCK : 1 ~> 0;
  }
}

function makeLock()
  requires true;
  ensures CASLock(r,ret,0) &*& r@(LOCK[1p]); {
    v := alloc(1);
    [v] := 0;
    return v;
}

function lock(x)
  requires CASLock(r,x,_) &*& r@(LOCK[p]);
  ensures CASLock(r,x,1) &*& r@(LOCK[p] * UNLOCK); {
    do {
        b := CAS(x, 0, 1);
    } while (b = 0);
}

function unlock(x)
  requires CASLock(r,x,1) &*& r@(UNLOCK);
  ensures CASLock(r,x,_); {
    [x] := 0;
}
