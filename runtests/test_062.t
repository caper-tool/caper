// NAME: Case split on consume conditional 2
// RESULT: ACCEPT

/* DESCRIPTION: This tests if Caper can perform a case split when consuming a conditional postcondition.
 */

function foo(x)
  requires x >= 0;
  ensures y + 1 = y + 2 ? false : true;
{
}
