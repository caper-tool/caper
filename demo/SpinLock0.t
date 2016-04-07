// Spin Lock

region SLock(r, x) {
  guards UNLOCK;
  interpretation {
    0 : x |-> 0 &*& r@UNLOCK;
    1 : x |-> 1;
  }
  actions {
           : 0 ~> 1;
    UNLOCK : 1 ~> 0;
  }
}


function makeLock()
{
    v := alloc(1);
    [v] := 0;
    return v;
}


function lock(x)
{
    do {
        b := CAS(x, 0, 1);
    }
    while (b = 0);
}

function unlock(x)
{
    [x] := 0;
}
