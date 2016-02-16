// NAME: Left-over permissions
// RESULT: ACCEPT


function foo()
  requires r@(A[p]);
  ensures r@(B[p]);
{
  foo();
}

function bar()
  requires r@(A[p]);
  ensures r@(B[p]);
{
  foo();
  foo();
}
