// NAME: Guarantee with parametrised transitions 3
// RESULT: ACCEPT

region Foo(r,x) {
  guards #FOO;
  interpretation {
    n : x |-> n;
  }
  actions {
    l < u | FOO{ i | l <= i, i <= u } : l ~> u;
  }
}

function foo(x, u)
  requires Foo(r,x,u-1) &*& r@(FOO{i | i <= u});
  ensures Foo(r,x,u) &*& r@(FOO{i | i <= u});
{
  [x] := u;
}

