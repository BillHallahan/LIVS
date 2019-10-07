function add(x, y) {
    return x + y
}

function mul(x, y) {
    return x * y
}

function addthree(x) {
    return x + 3
}

//@pbe (constraint (= (f 0 0) 0))
//@pbe (constraint (= (f 1 1) 3))
//@pbe (constraint (= (f 1 2) 11))
//@pbe (constraint (= (f 2 1) 5))
//@pbe (constraint (= (f 2 2) 14))
//@pbe (constraint (= (f 3 3) 39))
//@pbe (constraint (= (f 4 2) 20))

// return add(add(mul(y, mul(y, y)), x), mul(x, y))
// x + y^3 + xy
