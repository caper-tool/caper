// Counter Client

function thread_incr(x,y)
  requires Counter(r,x,_) &*& r@(AUTH|1| * INCR[p]) &*& Join(s,y,r,x,p,0) &*& s@SET;
  ensures true;
{
    incr(x);
    set(y);
}

function parallel_incr()
  requires true;
  ensures Counter(r,x,2) &*& r@(CONT|2| * AUTH|-1-2| * INCR[1p]);
{
  x := makeCounter();
  y1 := make_join();
  fork thread_incr(x,y1);
  y2 := make_join();
  fork thread_incr(x,y2);
  wait(y1);
  wait(y2);
  skip;
}

// Counter Library

region Counter(r,x) {
  guards %INCR * |CONT| * |AUTH|;
  interpretation {
    n : x |-> n &*& n >= 0 &*& r@(CONT|-1-n| * AUTH|n|);
  }
  actions {
    INCR[_] : n ~> m;
  }
}

function makeCounter()
  requires true;
  ensures Counter(r,ret,0) &*& r@(INCR[1p] * AUTH|-1|);
{
    x := alloc(1);
    [x] := 0;
    return x;
}

function incr(x)
  requires Counter(r,x,_) &*& r@(AUTH|1| * INCR[p]);
  ensures Counter(r,x,_) &*& r@(CONT|1| * INCR[p]);
{
    v := [x];
    b := CAS(x, v, v + 1);
    if (b = 0) {
       incr(x);
    }
}

// Fork Join Library

region Join(s,y,r,x,p) {
  guards SET * JOIN;
  interpretation {
    0 : y |-> 0;
    1 : y |-> 1 &*& (s@JOIN \/ Counter(r,x,_) &*& r@(CONT|1| * INCR[p]));
  }
  actions {
    SET : 0 ~> 1;
  }
}

function make_join()
  requires Counter(r,x,_) &*& p != 0p;
  ensures Join(s,ret,r,x,p,0) &*& s@(SET * JOIN);
{
    y := alloc(1);
    [y] := 0;
    return y;
}

function set(y)
  requires Counter(r,x,_) &*& r@(CONT|1| * INCR[p]) &*& Join(s,y,r,x,p,0) &*& s@SET;
  ensures Join(s,y,r,x,p,1);
{
    [y] := 1;
}

function wait(y)
  requires Counter(r,x,_) &*& s@JOIN &*& Join(s,y,r,x,p,_);
  ensures Counter(r,x,_) &*& r@(CONT|1| * INCR[p]) &*& Join(s,y,r,x,p,1);
{
    v := [y];
    if (v = 0) {
        wait(y);
    }
}
