// NAME: Invalid Guard Declaration in Region Declaration 2
// RESULT: REJECT

region Foo(r) {
        guards BAR + (FOO * BAR);
        interpretation {
                0 : true;
        }
        actions {
        }
}
