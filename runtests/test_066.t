// NAME: Case split on consume conditional 6
// RESULT: REJECT

/* DESCRIPTION: This tests if Caper can perform a case split when consuming a conditional postcondition.
 */

function foo(x)
  requires x >= 0;
  ensures (x = y ? false : false);
{
}
