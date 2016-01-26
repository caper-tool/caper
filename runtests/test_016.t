// NAME: Basic conditional test 2
// RESULT: REJECT

/* DESCRIPTION: Test the ?: behaviour
*/

function foo(x)
  requires x = 0 ? true : x = 1;
  ensures x = 0;
{
}
