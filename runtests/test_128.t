// NAME: Left-over permissions 2
// RESULT: ACCEPT


function foo()
  requires r@(A[p]);
  ensures r@(B[p]);
{
  foo();
}

function bar()
  requires r@A[p];
  ensures r@B[b] &*& p = a $ b;
{
  foo();
}
