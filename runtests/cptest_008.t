// NAME: G|n| ~> G|1|
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
  requires r@(G|n|);
  ensures  r@(G|1|);
{}