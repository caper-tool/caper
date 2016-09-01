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
                        \/ (k < waiters &*& a@(DOWN|-1-waiters+k| * WAIT(0) * WAIT{x|k<x,x<waiters})));
    0 < k, k <= waiters | -k : b |-> -k &*&
                      (a@(DOWN|-1-waiters+k| * WAIT{x|k<=x,x<waiters})
                        \/ (k < waiters &*& a@(UP|-1-waiters+k| * WAIT(0) * WAIT{x|k<x,x<waiters})));
  }
  actions {
    0<=k,k<n,n<=waiters  | UP|-waiters+n-1| * WAIT{x|k<=x,x<waiters} : k ~> n;
    waiters>=k,k>=n,n>=0 | WAIT(0) * WAIT{x|n<x,x<waiters} * DOWN|-1-waiters+k|  : k ~> n;
    0<=k,k<n,n<=waiters  | DOWN|-waiters+n-1| * WAIT{x|k<=x,x<waiters} : -k ~> -n;
    waiters>=k,k>=n,n>=0 | WAIT(0) * WAIT{x|n<x,x<waiters} * UP|-1-waiters+k|  : -k ~> -n;

    ////0<=k,k<waiters,waiters>=n,n>=0 | UP|-1| * WAIT(0) * WAIT{x|n<x,x<waiters} : k ~> n;

    //waiters>=k,k>0,0<n-1,n<=waiters | WAIT(0) * WAIT{x|n-1<=x,x<waiters} * DOWN|-1| : k ~> n;
    ////waiters>=k,k>=m,m>0,m<n,n<=waiters | WAIT(0) * WAIT{x|m<=x,x<waiters} * DOWN|-1| : k ~> n;
    //waiters>=k,k>=0,0<n,n<=waiters | WAIT(0) * WAIT{x|0<x,x<waiters} * DOWN|-1| : k ~> n;

    ////waiters>=k,k>=m,m>=0,m<n,n<=waiters | WAIT(0) * WAIT{x|m<=x,x<waiters,m!=0} * WAIT{x|m<x,x<waiters,m=0} * DOWN|-1| : k ~> n;

    //waiters>=k,k>=m,m>=0,m<waiters,waiters>=n,n>=0 | WAIT(0) * WAIT{x|m<x,x<waiters} * WAIT{x|n<x,x<=m} * DOWN|-1|  : k ~> n;



//    0<=k,k<=waiters,watiers>=n,n>=0 | UP|-1| * WAIT{x|0<x,x<waiters} : k ~> n;
//                         | WAIT(0) * WAIT{x|n<x,x<waiters} * DOWN|-1| : k ~> n

//0<=k,k<=k1,k1<waiters,k1>n,n>=0 | UP|-waiters+k1| * WAIT(0) * WAIT{x|n<x,x<waiters} : k ~> n;
/*    WAIT(0) : waiters ~> waiters - 1;
    n > 0 | WAIT(n) : n ~> n - 1;
    n>=0, n<waiters | DOWN|-waiters-n| : -n ~> -n - 1;
    WAIT(0) : -waiters ~> -waiters + 1;
    n > 0 | WAIT(n) : -n ~> -n + 1;*/
  }
}
/*
region Baz(r,a,b,waiters) {
  guards 0;
  interpretation {
    0 : ret = 0 &*& Barrier(a,b,waiters,s) &*& a@WAIT(ret) &*& ret >= 0 &*& ret < waiters &*& s = waiters;
    1 : Barrier(a,b,waiters,waiters-1) &*& a@WAIT(waiters - 1) &*& waiters > 1;
    2 : Barrier(a,b,waiters,waiters-2) &*& a@WAIT(waiters - 2) &*& waiters > 2;
    //1 : ret = 1 &*& Barrier(a,b,waiters,s) &*& a@WAIT(ret) &*& ret >= 0 &*& ret < waiters &*& s >= ret;
    //2 : ret = 2 &*& Barrier(a,b,waiters,s) &*& a@WAIT(ret) &*& ret >= 0 &*& ret < waiters &*& s >= ret;
    //3 : ret = 3 &*& Barrier(a,b,waiters,s) &*& a@WAIT(ret) &*& ret >= 0 &*& ret < waiters &*& s >= ret;
    //4 : Barrier(a,b,waiters,_) &*& a@DOWN|1|;
  }
  actions {}
}
*/

/*

function tester(b,waiters)
  requires Barrier(a,b,waiters,s) &*& s > 0 &*& a@WAIT(0);
  ensures Barrier(a,b,waiters,x) &*& x = waiters &*& a@WAIT(0);
{
  t := [b];
  if (b < waiters) {
    tester(b,waiters);
  } else {
    miracle();
  }
  //t := [b];
}*/
/*
function syncUpEnter(b,waiters)
  requires Barrier(a,b,waiters,_) &*& a@UP|1|;
  ensures Barrier(a,b,waiters,s) &*& a@WAIT(ret) &*& ret >= 0 &*& ret < waiters &*& s >= 0;
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
*/

// Explore: initially forgot z > 0
function sue(b,waiters,z)
  requires Barrier(a,b,waiters,z) &*& (z = waiters ? a@WAIT(waiters) : a@WAIT(z)) &*& z > 0;
  ensures Barrier(a,b,waiters,_) &*& a@DOWN|1|;
{
  [b] := z - 1;
}

function syncUpExit(b,waiters,w)
  requires Barrier(a,b,waiters,s) &*& a@WAIT(w) &*& w >= 0 &*& w < waiters &*& s >= 0;
  ensures Barrier(a,b,waiters,_) &*& a@DOWN|1|;
{
  z := [b];
  if ((w = 0 and z = waiters) or (w != 0 and z = w)) {
    assert w = 0 ? Barrier(a,b,waiters,waiters) : Barrier(a,b,waiters,w);
    [b] := z - 1;
    //miracle();
    /*cr := CAS(b,z,z-1);
    if (cr = 0) {
      syncUpExit(b,waiters,w);
    }*/
  } else {
    syncUpExit(b,waiters,w);
  }
}

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
