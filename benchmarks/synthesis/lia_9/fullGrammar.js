function add(x, y) {
    return x + y
}

function sub(x, y) {
    return x - y
}

function mul(x, y) {
    return x * y
}

//@pbe (constraint (= (f 0 0) 0))
//@pbe (constraint (= (f 1 1) 1))
//@pbe (constraint (= (f 1 2) -1))
//@pbe (constraint (= (f 2 1) 2))
//@pbe (constraint (= (f 2 2) -2))
//@pbe (constraint (= (f 3 3) -15))
//@pbe (constraint (= (f 4 2) -10))

// return sub(add(mul(x, y), sub(add((mul(x, x), y)), mul(y, mul(x, x)))), mul(y, y))
// x^2 + y - y(x^2) + xy - y^2
