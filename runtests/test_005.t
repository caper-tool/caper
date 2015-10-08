// NAME: boolean or (version 2)
// RESULT: ACCEPT

// DESCRIPTION: an implementation of boolean or

function bor2(a, b)
        requires a >= 0 &*& a <= 1 &*& b >= 0 &*& b <= 1;
        ensures ret >= a &*& ret >= b &*& ret <= a + b &*& ret <= 1 &*& ret >= 0;
{
         if (a = 0 and b = 0) { return 0; } return 1;
}
