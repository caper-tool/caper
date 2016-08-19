// NAME: G|n| * G|3| ~> G|n+3|
// RESULT: ACCEPT

// DESCRIPTION: 
region Foo(r) {
  guards |G|;
  interpretation {
    0 : true;
  }
  actions {}
}

function foo()
  requires r@(G|n| * G|3|);
  ensures  r@(G|n+3|);
{}