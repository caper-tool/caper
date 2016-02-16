// NAME: Sum guard test 2
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
  requires Foo(r, x, 0) &*& r@A;
  ensures Foo(r, x, 0) &*& r@B;
{
}
