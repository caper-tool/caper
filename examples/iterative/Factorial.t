// Factorial

function factorial(n)
  requires n >= 0;
  ensures n <= 1 ? ret = 1 : (n = 2 ? ret = 2 : (n = 3 ? ret = 6 : (n = 4 ? ret = 24 : (n = 5 ? ret = 120 : (n = 6 ? ret = 720 : (n = 7 ? ret = 5040 : (n = 8 ? ret = 40320 : (n = 9 ? ret = 362880 : (n = 10 ? ret = 3628800 : ret >= 3628800 * n)))))))));
{
    r := 1;
    i := 1;
    while (i <= n)
      invariant i >= 1 &*& i <= n + 1 &*& (i <= 2 ? r = 1 : (i = 3 ? r = 2 : (i = 4 ? r = 6 : (i = 5 ? r = 24 : (i = 6 ? r = 120 : (i = 7 ? r = 720 : (i = 8 ? r = 5040 : (i = 9 ? r = 40320 : (i = 10 ? r = 362880 : (i = 11 ? r = 3628800 : (i = 12 ? r = 39916800 : r >= 39916800 * (i - 2))))))))))));
    {
        r := r * i;
        i := i + 1;
    }
    return r;
}
