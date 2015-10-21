// NAME: Unstable region in assertions
// RESULT: ACCEPT

/* DESCRIPTION: A specification { P } _ { Q } where the assertions are not
        self-stable should be interperted as:
                forall F. { wssa(P * F) } _ { wssa(Q * F) }
        where wssa(P) is the weakest stable stronger assertion than P, and F
        is stable.
*/

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

