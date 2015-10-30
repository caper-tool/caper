// NAME: modulo-n
// RESULT: ACCEPT

// DESCRIPTION: compute the remainder modulo n

function lemma(x, n, y)
        requires y + n * (m + 1) = x;
        ensures y + n * k = x &*& k = (m + 1);
{
}

function mod(x, n)
        requires x >= 0 &*& n > 0;
        ensures ret + n * m = x &*& 0 <= ret &*& ret < n;
{
        if (x < n) {
                return x;
        } else {
                r := mod(x - n, n);
                lemma(x, n, r);
                return r;
        }
}


