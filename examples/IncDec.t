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
}

region Barrier(t,b,r,waiters) {
  guards #WAIT;
  interpretation {
    0 : b |-> waiters &*& (b+1) |-> k &*& k >= 0 &*& k < waiters &*& t@WAIT{x|k <= x, x < waiters} &*& UpDown(r,_,_) &*& r@INC|-1-k|;
    1 : b |-> waiters &*& (b+1) |-> (waiters - k) &*& k >= 0 &*& k < waiters &*& t@WAIT{x|0 <= x, x < k} &*& UpDown(r,_,_) &*& r@DEC|-1-k|;
    2 : b |-> waiters &*& (b+1) |-> k &*& k >= 0 &*& k < waiters &*& t@WAIT{x|k <= x, x < waiters} &*& UpDown(r,_,_) &*& r@DEC|-1-k|;
    3 : b |-> waiters &*& (b+1) |-> (waiters - k) &*& k >= 0 &*& k < waiters &*& t@WAIT{x|0 <= x, x < k} &*& UpDown(r,_,_) &*& r@INC|-1-k|;
  }
  actions {
    0 <= m, m <= 3 | WAIT{x|0 <= x, x < waiters} : n ~> m;
    : 1 ~> 2;
    : 3 ~> 0;
  }
}


function sync1(b)
  requires Barrier(t,b,r,n,_) &*& r@INC|1|;
  ensures Barrier(t,b,r,n,_) &*& r@DEC|1|;
{
  waiters := [b];
  do {
    k := [b + 1];
    z := CAS(b+1, k, k + 1);
  }
  invariant z = 0 ? Barrier(t,b,r,waiters,_) &*& r@INC|1| : Barrier(t,b,r,waiters,1) &*& t@WAIT(k);
  while (z = 0);
  miracle();
  do {
    l := [b + 1];
  }
  while (l != waiters - k);
  [b] := l - 1;
}

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
