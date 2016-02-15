// NAME: Guarantee with parametrised transitions 1
// RESULT: REJECT

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
  requires Foo(r,x,l) &*& r@(FOO(l) * FOO(u));
  ensures Foo(r,x,u) &*& r@(FOO(l) * FOO(u));
{
  [x] := u;
}

