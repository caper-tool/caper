// NAME: Permission guard test 4
// RESULT: ACCEPT

function foo()
  requires r@GUARD[1p];
  ensures r@GUARD[v] &*& r@GUARD[w] &*& v $ w = 1p;
{
}
