region Barrier(a,b,waiters) {
  guards #WAIT * (|UP| + |DOWN|);
  interpretation {
    -waiters <= k, k <= waiters | k : b |-> k &*&
                  (0 <= k &*&
                      (a@(UP|-1-waiters+k| * WAIT{x|k<=x,x<waiters})
                        \/ (k < waiters &*& a@(DOWN|-1-waiters+k| * WAIT(0) * WAIT{x|k<x,x<waiters})))
                    \/ 0 >= k &*& (a@(DOWN|-1-waiters-k| * WAIT{x| -k<=x,x<waiters})
                        \/ (-k < waiters &*& a@(UP|-1-waiters-k| * WAIT(0) * WAIT{x| -k<x,x<waiters}))));

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

function syncUpExit(b,waiters,w)
  requires Barrier(a,b,waiters,s) &*& a@WAIT(w) &*& w >= 0 &*& w < waiters &*& s >= 0;
  ensures Barrier(a,b,waiters,_) &*& a@DOWN|1|;
{
  z := [b];
  if ((w = 0 and z = waiters) or (w != 0 and z = w)) {
    [b] := z - 1;
  } else {
    syncUpExit(b,waiters,w);
  }
}

function syncUp(b,waiters)
  requires Barrier(a,b,waiters,_) &*& a@UP|1|;
  ensures a@DOWN|1|;
{
  w := syncUpEnter(b,waiters);
  syncUpExit(b,waiters,w);
}

function syncDownEnter(b,waiters)
  requires Barrier(a,b,waiters,_) &*& a@DOWN|1|;
  ensures Barrier(a,b,waiters,s) &*& a@WAIT(ret) &*& ret >= 0 &*& ret < waiters &*& s <= 0;
{
  z := [b];
  if (z <= 0) {
    cr := CAS(b,z,z-1);
    if (cr != 0) {
      return -z;
    }
  }
  z := syncDownEnter(b,waiters);
  return z;
}

function syncDownExit(b,waiters,w)
  requires Barrier(a,b,waiters,s) &*& a@WAIT(w) &*& w >= 0 &*& w < waiters &*& s <= 0;
  ensures Barrier(a,b,waiters,_) &*& a@UP|1|;
{
  z := [b];
  if ((w = 0 and z = -waiters) or (w != 0 and z = -w)) {
    [b] := z + 1;
  } else {
    syncDownExit(b,waiters,w);
  }
}

function syncDown(b,waiters)
  requires Barrier(a,b,waiters,_) &*& a@DOWN|1|;
  ensures a@UP|1|;
{
  w := syncDownEnter(b,waiters);
  syncDownExit(b,waiters,w);
}

function sync(b,waiters,d)
  requires Barrier(a,b,waiters,_) &*& (d = 0 ? a@UP|1| : a@DOWN|1|);
  ensures d = 0 ? ret = 1 &*& a@DOWN|1| : ret = 0 &*& a@UP|1|;
{
  if (d = 0) {
    syncUp(b,waiters);
    return 1;
  } else {
    syncDown(b,waiters);
    return 0;
  }
}

region Mediator(r,updown,barrier) {
  guards 0;
  interpretation {
    0 : n >= 0 &*& UpDown(updown,_,_) &*& Barrier(barrier,_,_,_) &*& (updown@INC|-1-n| &*& barrier@UP|n| \/ updown@DEC|-1-n| &*& barrier@DOWN|n|);
  }
  actions {}
}

region UpDown(r,x) {
  guards |INC| + |DEC|;
  interpretation {
    n : x |-> n;
  }
  actions {
    n < m | INC|1| : n ~> m;
    n > m | DEC|1| : n ~> m;
  }
}

function inc(x)
  requires UpDown(r,x,n) &*& r@INC|1|;
  ensures UpDown(r,x,m) &*& m > n &*& r@INC|1|;
{
  old := [x];
  r := CAS(x,old,old+1);
  if (r = 0) {
    inc(x);
  }
}

function dec(x)
  requires UpDown(r,x,n) &*& r@DEC|1|;
  ensures UpDown(r,x,m) &*& m < n &*& r@DEC|1|;
{
  old := [x];
  r := CAS(x,old,old-1);
  if (r = 0) {
    dec(x);
  }
}

function checkInc(x)
  requires UpDown(r,x,_) &*& r@INC|1|;
  ensures r@INC|1|;
{
  a := [x];
  b := [x];
  if (b < a) {
    x := [-1];
  }
}

function checkDec(x)
  requires UpDown(r,x,_) &*& r@DEC|1|;
  ensures r@DEC|1|;
{
  a := [x];
  b := [x];
  if (b > a) {
    x := [-1];
  }
}

function createUpDown()
  requires true;
  ensures UpDown(r,ret,0) &*& r@INC|-1|;
{
  x := alloc(1);
  [x] := 0;
  return x;
}
