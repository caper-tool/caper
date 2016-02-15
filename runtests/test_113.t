// NAME: Guarantee with parametrised transitions 4
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
  requires Foo(r,x,u-1) &*& r@(FOO{i | l <= i, i <= u}) &*& l + 10 = u;
  ensures Foo(r,x,u) &*& r@(FOO{i | l <= i, i <= u});
{
  [x] := u;
}

