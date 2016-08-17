// NAME: Guard type checking 3
// RESULT: ACCEPT

// DESCRIPTION: Tests guard type checking

region Foo(r) {
  guards #A + #B;
  interpretation {
    0 : true;
  }
  actions {
  }
}

function foo()
  requires Foo(r,0) &*& r@(A{x|z1 != 0} * B{x|z2 != 0});
  ensures z1 = 0 \/ z2 = 0;
{
}
