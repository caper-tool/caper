// NAME: boolean or (version 1)
// RESULT: ACCEPT

// DESCRIPTION: a specifiction for boolean or

function bor(a, b)
        requires a >= 0 &*& a <= 1 &*& b >= 0 &*& b <= 1;
        ensures ret >= a &*& ret >= b &*& ret <= a + b &*& ret <= 1 &*& ret >= 0;
{
        if (a = 1) {
                return 1;
        }
        if (b = 1) {
                return 1;
        }
        return 0;
}
