// NAME: Loop test 3
// RESULT: REJECT

/* DESCRIPTION:
*/

function foo(x)
  requires true;
  ensures x <= 0;
{
  while (x > 0)
  invariant true
  {
    x := -1;
  }
}
