// NAME: {true} skip {false}
// RESULT: REJECT

// DESCRIPTION: a function with empty body should not satisfy {true} f() {false}

function f()
        requires true;
        ensures false;
{
}
