// NAME: { true } skip { r@(G|0|) * Foo(r,0) }
// RESULT: ACCEPT

// DESCRIPTION: Producing the full guard on region creation
region Foo(r) {
  guards |G|;
  interpretation {
    0 : true;
  }
  actions {}
}

function foo()
  requires true;
  ensures  r@(G|0|) &*& Foo(r,0);
{}