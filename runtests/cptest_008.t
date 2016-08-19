// NAME: G|n| ~/~> G|1|
// RESULT: REJECT

// DESCRIPTION: can always create a share, if not neutral
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