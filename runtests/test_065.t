// NAME: Case split on consume conditional 5
// RESULT: REJECT

/* DESCRIPTION: This tests if Caper can perform a case split when consuming a conditional postcondition.
 */

function foo(x)
  requires x >= 0;
  ensures y = y &*& (x = y ? false : false);
{
}
