function add(x, y) {
    return x + y
}

function mul(x, y) {
    return x * y
}

//@pbe (constraint (= (f 0 0) 0))
//@pbe (constraint (= (f 1 1) 5))
//@pbe (constraint (= (f 1 2) 11))
//@pbe (constraint (= (f 2 1) 12))
//@pbe (constraint (= (f 2 2) 22))
//@pbe (constraint (= (f 3 3) 57))
//@pbe (constraint (= (f 4 2) 62))

// return add(add(mul(x, y), add(add((mul(x, x), y)), mul(y, mul(x, x)))), mul(y, y))
// x^2 + y + y(x^2) + xy + y^2
