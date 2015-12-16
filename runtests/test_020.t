// NAME: Loop test 3
// RESULT: REJECT

/* DESCRIPTION: In the ensures assertion, x refers to the value
     passed to the function call, not the value of the program
     variable (since the language is call-by-value).  This case
     checks that the logical variable is treated correctly.
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
