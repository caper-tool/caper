region SLock(r,x) {
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

function foo(x)
        requires SLock(r,x,0);
        ensures SLock(r,x,0);
{
}

