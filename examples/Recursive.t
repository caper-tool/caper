// Recursive examples

function factorial(n) {
    if (n = 0) {
        return 1;
    } else {
        m := factorial(n - 1);
        return n * m;
    }
}

function fibonacci(n) {
    if (n <= 1) {
        return 1;
    } else {
        m := fibonacci(n - 1);
        p := fibonacci(n - 2);
        return m + p;
    }
}
