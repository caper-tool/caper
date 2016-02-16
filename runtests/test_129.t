// NAME: Combine permissions
// RESULT: ACCEPT


function foo()
  requires r@A[a] &*& r@A[b] &*& p = a $ b;
  ensures r@A[p];
{
}
