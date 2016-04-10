// Join Library

region Join(r, x) {
  guards SET;
  interpretation {
    0 : x |-> 0;
    1 : x |-> 1;
  }
  actions {
    SET : 0 ~> 1;
  }
}

function make_join()
  requires true;
  ensures Join(r, ret, 0) &*& r@SET;
{
    v := alloc(1);
    [v] := 0;
    return v;
}

function set(x)
  requires Join(r, x, 0) &*& r@SET;
  ensures Join(r, x, 1);
{
    [x] := 1;
}

function wait(x)
  requires Join(r, x, _);
  ensures Join(r, x, 1);
{
    do {
        v := [x];
    }
      invariant Join(r, x, w) &*& (v = 0 ? w >= 0 : w = 1);
    while (v = 0);
}

region Flag(r, x, y) {
  guards SFLAG;
  interpretation {
    0 : x |-> 0 &*& Join(s, y, 0) &*& s@SET;
    1 : x |-> 1 &*& Join(s, y, _);
  }
  actions {
    SFLAG : 0 ~> 1;
  }
}

function thread1(x, y)
  requires Flag(r, x, y, 0) &*& r@SFLAG;
  ensures true;
{
  [x] := 1;
  set(y);
}

function set_flag(x)
  requires x |-> 0;
  ensures ret = 1;
{ 
  y := make_join();
  fork thread1(x, y);
  wait(y);
  v := [x];
  return v;
}

