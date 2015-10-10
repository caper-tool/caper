// NAME: {true} diverge {false}
// RESULT: ACCEPT

// DESCRIPTION: a infinitely recursing function satisfies {true} f() {false}

function f()
        requires true;
        ensures false;
{
        f();
}

