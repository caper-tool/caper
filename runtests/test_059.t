// NAME: Region in region 4
// RESULT: ACCEPT

/* DESCRIPTION: This test is equivalent to test_058, however at present Caper fails
 * to accept a region definitions that include another region conditionally.
 */

region Ra(r, x) {
  guards 0;
  interpretation {
    n >= 0 | n : x |-> n &*& (n = 0 ? true : Ra(r, n, _));
  }
  actions {
  }
}
