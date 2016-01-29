// Factorial

function factorial(n)
  requires n >= 0;
  ensures n <= 1 ? ret = 1 : (n = 2 ? ret = 2 : (n = 3 ? ret = 6 : (n = 4 ? ret = 24 : (n = 5 ? ret = 120 : (n = 6 ? ret = 720 : (n = 7 ? ret = 5040 : (n = 8 ? ret = 40320 : (n = 9 ? ret = 362880 : (n = 10 ? ret = 3628800 : ret >= 3628800 * n)))))))));
{
    if (n = 0) {
        return 1;
    } else {
        m := factorial(n - 1);
        return n * m;
    }
}
