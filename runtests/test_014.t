// NAME:
// RESULT:

/* DESCRIPTION:
*/

region Ra(r,x) {
  guards FOO;
  interpretation {
    0 : x |-> 0;
    1 : x |-> 1;
    2 : x |-> 2;
  }
  actions {
    BAR : n ~> n + 1;
  }
}
