// Join Library

region Join(r,x) {
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
  ensures Join(r, ret, 0) &*& r@(SET);
{
    v := alloc(1);
    [v] := 0;
    return v;
}

function set(x)
  requires Join(r, x, 0) &*& r@(SET);
  ensures Join(r, x, 1);
{
    [x] := 1;
}

function wait(x)
  requires Join(r, x, _);
  ensures Join(r, x, 1);
{
    do
      invariant Join(r, x, w) &*& (v = 0 ? w >= 0 : w = 1);
    {
        v := [x];
    } while (v = 0);
}