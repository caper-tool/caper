// NAME: Zero-guard test 4
// RESULT: ACCEPT

region SLock(r, x) {
  guards UNLOCK;
  interpretation {
    0 : x |-> 0 &*& r@UNLOCK;
    1 : x |-> 1;
  }
  actions {
    0 : 0 ~> 1;
    UNLOCK : 1 ~> 0;
  }
}

function lock_rec(x)
  requires SLock(r, x, _);
  ensures SLock(r, x, 1) &*& r@UNLOCK;
{
    b := CAS(x, 0, 1);
    if (b = 0) {
        lock_rec(x);
    }
}