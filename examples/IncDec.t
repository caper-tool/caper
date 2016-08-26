/*
region UpDown(r,x) {
  guards |INC| + |DEC| + OWN;
  interpretation {
    n : x |-> n;
  }
  actions {
    n < m | INC|1| : n ~> m;
    n > m | DEC|1| : n ~> m;
    OWN : n ~> m; // Required for transitivity check
  }
}*/

region Barrier(a,b,waiters) {
  guards #WAIT * (|UP| + |DOWN|);
  interpretation {
    0 <= k, k <= waiters | k : b |-> k &*&
                      (a@(UP|-1-waiters+k| * WAIT{x|k<=x,x<waiters})
                        \/ a@(DOWN|-1-waiters+k| * WAIT{x|x=0,k<waiters} * WAIT{x|k<x,x<waiters}));
    0 < k, k <= waiters | -k : b |-> -k &*&
                      (a@(DOWN|-1-waiters+k| * WAIT{x|k<=x,x<waiters})
                        \/ a@(UP|-1-waiters+k| * WAIT{x|x=0,k<waiters} * WAIT{x|k<x,x<waiters}));
  }
  actions {
    0<=k,k<n,n<=waiters  | UP|-waiters+n-1| * WAIT{x|k<=x,x<waiters} : k ~> n;
    waiters>=k,k>=n,n>=0 | WAIT(0) * WAIT{x|n<x,x<waiters} * DOWN|-1-waiters+k|  : k ~> n;
    0<=k,k<n,n<=waiters  | DOWN|-waiters+n-1| * WAIT{x|k<=x,x<waiters} : -k ~> -n;
    waiters>=k,k>=n,n>=0 | WAIT(0) * WAIT{x|n<x,x<waiters} * UP|-1-waiters+k|  : -k ~> -n;
  }
}


function syncUpEnter(b,waiters)
  requires Barrier(a,b,waiters,_) &*& a@UP|1|;
  ensures Barrier(a,b,waiters,s) &*& a@WAIT(ret) &*& s > 0;
{
  z := [b];
  if (z >= 0) {
    cr := CAS(b,z,z+1);
    if (cr != 0) {
      return z;
    }
  }
  z := syncUpEnter(b,waiters);
  return z;
}
/*
function syncUpExit(b,waiters,w)
  requires Barrier(a,b,waiters,s) &*& a@WAIT(w) &*& s >= 0 &*& s <= 1;
  ensures Barrier(a,b,waiters,_) &*& a@DOWN|1|;
{
  z := [b];
  if ((w = 0 and z = waiters) or (w != 0 and z = w)) {
    cr := CAS(b,z,z-1);
    if (cr = 0) {
      syncUpExit(b,waiters,w);
    }
  } else {
    syncUpExit(b,waiters,w);
  }
}
*/
/*
function syncUp(b,waiters)
  requires Barrier(a,b,waiters,_) &*& a@UP|1|;
  ensures u@DOWN|1|;
{
  do {
    z := [b];
    if (z >= 0) {
      cr := CAS(b,z,z+1);
    } else {
      cr := 0;
    }
  }
    invariant Barrier(a,b,waiters,_) &*& (cr = 0 ? u@UP|1| : a@WAIT(z));
  while (cr = 0);
  miracle();
}
*/
function fault()
{
  x := [-1];
}

function miracle()
  requires true;
  ensures false;
{
  miracle();
}
