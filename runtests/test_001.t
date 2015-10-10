// NAME: {true} skip {true}
// RESULT: ACCEPT

// DESCRIPTION: a function with empty body satisfies {true} f() {true}

function f()
        requires true;
        ensures true;
{
}

