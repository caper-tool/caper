// NAME: { G|0| } skip { G|0| }
// RESULT: ACCEPT

// DESCRIPTION: basic parsing of counting guard algebra declaration
region Foo(r) {
  guards |G|;
  interpretation {
    0 : true;
  }
  actions {}
}

function foo()
  requires r@(G|0|);
  ensures  r@(G|0|);
{}