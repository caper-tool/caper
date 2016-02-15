// NAME: Guarantee with parametrised transitions 2
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
  requires Foo(r,x,l) &*& r@(FOO(l) * FOO(u)) &*& u = l + 1;
  ensures Foo(r,x,u) &*& r@(FOO(l) * FOO(u));
{
  [x] := u;
}

