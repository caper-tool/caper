// NAME: Loop test 1
// RESULT: ACCEPT

/* DESCRIPTION:
*/

function foo(x)
  requires true;
  ensures x <= 0;
{
  while (x > 0)
  invariant true
  {
  }
}
