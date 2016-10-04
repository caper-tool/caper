// NAME: G|-1| ~> G|-2| * G|1|
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
  requires r@(G|-1|);
  ensures  r@(G|-2| * G|1|);
{}