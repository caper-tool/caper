region RWLock(r,x) {
  guards %WLOCK * WUNLOCK * %RLOCK * |RUNLOCK|;
  interpretation {
    n > -1 | n : x |->  n &*& r@(WUNLOCK * RUNLOCK|-(n+1)|);
            -1 : x |-> -1 &*& r@(RUNLOCK|-1|);
  }
  actions {
               WLOCK[_] :       0 ~>    -1;
               WUNLOCK  :      -1 ~>     0;
    n > -1, m > 0 | RUNLOCK|m| : n + m ~>     n;
    m > 0 | RLOCK[_] * WUNLOCK :    -1 ~> m;
             : n ~> n;
    n > -1, m > 0, k + m > n | RLOCK[_] * RUNLOCK|m| : n ~> k;
     m > 0, k + m > 0 | WUNLOCK * RLOCK[_] * RUNLOCK|m| : -1 ~> k;
    n > -1, m > n |   RLOCK[_] :    n ~> m;
    n > 0 | WLOCK[_] * RUNLOCK|n|    : n ~> -1;
    n > -1,m > n | RLOCK[_] * WLOCK[_] * RUNLOCK|m| : n ~> -1;
  }
}

function makeLock()
  requires true;
  ensures RWLock(r,ret,_) &*& r@(WLOCK[1p] * RLOCK[1p]);
{
  v := alloc(1);
  [v] := 0;
  return v;
}

function readerEntry(x)
  requires RWLock(r,x,_) &*& r@RLOCK[p];
  ensures  RWLock(r,x,n) &*& n > 0 &*& r@(RLOCK[p] * RUNLOCK|1|);
{
  v := [x];
  if (v >= 0) {
    b := CAS(x, v, v + 1);
    if (b != 0) {
      return;
    }
  }
  readerEntry(x);
}


// function writerEntry(x)
//   requires RWLock(r,x,_) &*& r@WLOCK[p];
//   ensures RWLock(r,x,-1) &*& r@(WLOCK[p] * WUNLOCK);
// {
//   b := CAS(x, 0, -1);
//   if (b = 0) {
//     writerEntry(x);
//   }
// }

// function writerExit(x)
//   requires RWLock(r,x,-1) &*& r@WUNLOCK;
//   ensures RWLock(r,x,_);
// {
//   [x] := 0;
// }


function readerExit()
  requires true;
  ensures true;
{
}