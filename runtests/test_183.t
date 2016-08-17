// NAME: Guard type checking 2
// RESULT: ACCEPT

// DESCRIPTION: Tests guard type checking

region Foo(r) {
  guards A;
  interpretation {
    0 : true;
  }
  actions {
  }
}

function foo()
  requires Foo(r,0) &*& r@A[0p];
  ensures false;
{
}
