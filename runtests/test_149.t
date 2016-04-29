// NAME: Duplicate region declaration test
// RESULT: REJECT

region SLock(r, x) {
  guards UNLOCK;
  interpretation {
    0 : x |-> 0 &*& r@UNLOCK;
    1 : x |-> 1;
  }
  actions {
    : 0 ~> 1;
    UNLOCK : 1 ~> 0;
  }
}
region SLock(r, x) {
  guards 0;
  interpretation {
    0 : x |-> 0;
  }
  actions {
  }
}

