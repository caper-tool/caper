// NAME: Sum guard test 5
// RESULT: REJECT

region Foo(r, x) {
  guards A + B;
  interpretation {
    0 : x |-> 0 &*& r@B;
    1 : x |-> 1;
  }
  actions {
    A: 0 ~> 1;
    A: 1 ~> 0;
  }
}

function foo()
  requires true;
  ensures Foo(r, ret, 0) &*& r@A;
{
    x := alloc(1);
    [x] := 0;
    return x;
}
