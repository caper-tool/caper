// NAME: { true } skip { Foo(r,0) &*& r@(G|-1|) }
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
  ensures  Foo(r,0) &*& r@(G|-1|);
{}
