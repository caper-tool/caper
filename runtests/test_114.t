// NAME: Guarantee with parametrised transitions 5
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
  requires Foo(r,x,u-1) &*& r@(FOO{i | l <= i, i <= u}) &*& l + 10 = u;
  ensures true;
{
  [x] := u+1;
}

