// NAME: Sum guard test 1
// RESULT: ACCEPT

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

function foo()
  requires true;
  ensures Foo(r, x, 0) &*& r@B;
{
    x := alloc(1);
    [x] := 0;
    return x;
}
