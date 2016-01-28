// NAME: Misused Guards in Region Declaration 3
// RESULT: REJECT

region Ra(r,x) {
  guards 0;
  interpretation {
    0 : x |-> 0 &*& r@(GUARD);
  }
  actions {
  }
}
