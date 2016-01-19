// Parallel Increment

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

functiom wait(x)
  requires Join(r, x, _);
  requires Join(r, x, 1);
{
    do {
        v := [x];
    } while (v = 0);
}

function weak_incr(x, y)
  requires x |-> v0 &*& Join(r, j, 0) &*& r@(SET);
  ensures x |-> v0 + 1 &*& Join(r, j, 1);
{
    v := [x];
    [x] := v + 1;
    set(j);
    return v;
}

function incr(x, y)
  requires x |-> v0 &*& Join(r, j, 0) &*& r@(SET);
  ensures x |-> v0 + 1 &*& Join(r, j, 1);
{
    do 
        invariant x |-> vi &*& (b != 0 ? vi = (v0 + 1) : vi = v0)
    {
        v := [x];
        b := CAS(x, v, v + 1);
    } while (b = 0);
    set(j);
    return v;
}

function parallel_incr(x, y)
  requires x |-> v0 &*& y |-> w0;
  ensures x |-> v0 + 1 &*& y |-> w0 + 1;
{
    j1 := make_join();
    j2 := make_join();
    fork weak_incr(x, j1);
    fork weak_incr(y, j2);
    wait(j1);
    wait(j2);
}

function parallel_incr2(x, y)
  requires x |-> v0 &*& y |-> w0;
  ensures x |-> v0 + 1 &*& y |-> w0 + 1;
{
    j1 := make_join();
    j2 := make_join();
    fork incr(x, j1);
    fork incr(y, j2);
    wait(j1);
    wait(j2);
}
