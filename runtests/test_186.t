// NAME: Guard type checking 5
// RESULT: ACCEPT

// DESCRIPTION: Tests guard type checking

region Foo(r) {
  guards A + B;
  interpretation {
    0 : true;
  }
  actions {
  }
}

function foo()
  requires Foo(r,0) &*& r@(A * B);
  ensures false;
{
}
