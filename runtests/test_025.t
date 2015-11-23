// NAME: Invalid Guard Declaration in Region Declaration 1
// RESULT: REJECT

region Foo(r) {
        guards BAR * BAR;
        interpretation {
                0 : true;
        }
        actions {
        }
}
