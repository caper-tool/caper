// Recursive examples

function factorial(n) {
    var m;
    if (n = 0) {
        return 1;
    } else {
        m := factorial(n - 1);
        return n * m;
    }
}

function fibonacci(n) {
    var m, p;
    if (n <= 1) {
        return 1;
    } else {
        m := fibonacci(n - 1);
        p := fibonacci(n - 2);
        return m + p;
    }
}
