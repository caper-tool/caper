// NAME: Guard type checking 1
// RESULT: ACCEPT

// DESCRIPTION: Tests guard type checking

region Foo(r) {
  guards %A;
  interpretation {
    0 : true;
  }
  actions {
  }
}

function foo()
  requires r@A &*& Foo(r,0);
  ensures false;
{
}
