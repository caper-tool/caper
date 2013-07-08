// Compare-and-swap lock

function makeLock()
  requires emp;
  ensures IsLock(x) * ret = x; {
    var v;
    v := alloc(1);
    [v] := 0;
    return v;
}

function lock(x)
  requires IsLock(x);
  ensures Locked(x); {
    var b;
    do {
        b := CAS(x, 0, 1);
    } while (b = 0);
}

function unlock(x)
  requires Locked(x);
  ensures isLock(x); {
    [x] := 0;
}
