// NAME: Region in region 3
// RESULT: ACCEPT

/* DESCRIPTION: We can put a region into a region in a way that is consistent
 */

region Ra(r, x) {
  guards 0;
  interpretation {
    0 : x |-> 0;
    n > 0 | n : x |-> n &*& Ra(r, n, _);
  }
  actions {
  }
}
