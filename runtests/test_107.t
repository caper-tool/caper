// NAME: Stability with parametrised transitions 2
// RESULT: REJECT

region Foo(r,x) {
  guards #FOO;
  interpretation {
    n : x |-> n;
  }
  actions {
    l < u | FOO{ i | l <= i, i < u } : l ~> u;
  }
}

region Bar(r,x) {
  guards 0;
  interpretation {
    0 : Foo(s,x,k) &*& k < 4 &*& s@(FOO(7));
  }
  actions {
  }
}
