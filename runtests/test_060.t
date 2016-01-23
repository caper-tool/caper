// NAME: Simplified region/conditional
// RESULT: ACCEPT

/* DESCRIPTION: Based on test_059, this is a slightly simplified conditional test.
 */

region Ra(r) {
  guards 0;
  interpretation {
    n >= 0 | n : (n = 0 ? true : Ra(r, n));
  }
  actions {
  }
}
