// NAME: G|1| * G|-1| inconsistent
// RESULT: ACCEPT

// DESCRIPTION: 
region R(r) {
  guards |G|;
  interpretation {
    0 : true;
  }
  actions {}
}

function foo()
  requires R(r,0) &*& r@(G|-1|) &*& r@(G|1|);
  ensures  false;
{}