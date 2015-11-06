// NAME: Basic conditional test 1
// RESULT: ACCEPT

/* DESCRIPTION: Test the ?: behaviour
*/

function foo(x)
  requires x = 0 ? true : x = 0;
  ensures x = 0;
{
}
