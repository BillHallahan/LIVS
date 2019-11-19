function add(x, y) {
    return x + y
}

function sub(x, y) {
    return x - y
}

function mul(x, y) {
    return x * y
}

function addeight(x) {
    return x + 8
}

function timesfour(x) {
    return x * 4
}

function timesfourteen(x) {
    return x * 14
}

function timesfive(x) {
    return x * 5
}

//@pbe (constraint (= (f 0 0) 8))
//@pbe (constraint (= (f 1 1) 26))
//@pbe (constraint (= (f 1 2) 38))
//@pbe (constraint (= (f 2 1) 39))
//@pbe (constraint (= (f 2 2) 52))
//@pbe (constraint (= (f 3 3) 86))

// return sub(add(mul(x, y), addeight(add(timesfour(mul(x, x)), timesfourteen(y)))), mul(y, y))
// 4x^2 + 14y + 8 + xy - y^2
