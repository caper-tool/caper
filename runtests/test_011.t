// NAME: too many arguments
// RESULT: REJECT

// DESCRIPTION: The precondition for foo should be rejected since it gives too
//      many arguments to the SLock region.

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
        requires SLock(r,z,k,0);
        ensures SLock(r,z,0);
{
}

