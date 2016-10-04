// NAME: Empty guards and +
// RESULT: ACCEPT
// DESCRIPTION: This can expose a problem if Caper is over-eager to
//      rewrite guards.

region Test(r) {
    guards |U| + |D|;
    interpretation {
        0 : true;
    }
    actions {}
}

function a()
    requires Test(r,0) &*& r@U|1| &*& r@D|0|;
    ensures Test(r,0) &*& r@U|1|;
{
}

function b()
    requires Test(r,0) &*& r@D|1| &*& r@U|0|;
    ensures Test(r,0) &*& r@D|1|;
{
}
