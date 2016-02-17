// NAME: Permission guard test 1
// RESULT: REJECT

function foo()
  requires r@GUARD[1p];
  ensures r@GUARD[v] &*& r@GUARD[v] &*& v $ v = 1p;
{
}
