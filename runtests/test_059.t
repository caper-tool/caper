// NAME: Region in region 4
// RESULT: ACCEPT

/* DESCRIPTION: This test is equivalent to test_058, but with a conditional
 * inside the interpretation.  This test concerns issue #7.
 */

region Ra(r, x) {
  guards 0;
  interpretation {
    n >= 0 | n : x |-> n &*& (n = 0 ? true : Ra(r, n, _));
  }
  actions {
  }
}
