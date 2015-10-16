// NAME: modulo-two
// RESULT: ACCEPT

// DESCRIPTION: compute the remainder modulo 2

function mod2(x)
        requires x >= 0;
        ensures ret + 2 * n = x &*& 0 <= ret &*& ret < 2;
{
        if (x < 2) {
                return x;
        } else {
                r := mod2(x - 2);
                return r;
        }
}
