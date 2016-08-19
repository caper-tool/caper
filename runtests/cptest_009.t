// NAME: G|n| ~> G|1|, n != 0
// RESULT: ACCEPT

// DESCRIPTION: can always create a share, if not neutral
region Foo(r) {
  guards |G|;
  interpretation {
    0 : true;
  }
  actions {}
}

function foo()
  requires r@(G|n|) &*& n != 0;
  ensures  r@(G|1|);
{}