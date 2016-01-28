// NAME: Misused Guards in Region Declaration 3
// RESULT: ACCEPT

/* Description: The interpretation for state 0 is equivalent to false, as the guard does not exist.
 */

region Ra(r,x) {
  guards 0;
  interpretation {
    0 : x |-> 0 &*& r@(GUARD);
  }
  actions {
  }
}
