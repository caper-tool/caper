// NAME: Sum guard test 4
// RESULT: REJECT

region Foo(r, x) {
  guards A + B;
  interpretation {
    0 : x |-> 0;
    1 : x |-> 1;
  }
  actions {
    A: 0 ~> 1;
    A: 1 ~> 0;
  }
}

function foo(x)
  requires Foo(r, x, 0) &*& r@B;
  ensures Foo(r, x, 1) &*& r@A &*& r@B;
{
    [x] := 1;
}
