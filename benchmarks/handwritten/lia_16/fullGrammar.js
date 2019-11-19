function complex_one(x) {
    return x + (x * x * 2) - 3
}

function complex_two(x) {
    return (x * x * 3) - x + 2
}

function add(x, y) {
    return x + y
}

//@pbe (constraint (= (f 0 0) -1))
//@pbe (constraint (= (f 1 1) 4))
//@pbe (constraint (= (f 1 2) 12))
//@pbe (constraint (= (f 2 1) 11))
//@pbe (constraint (= (f 2 2) 19))
//@pbe (constraint (= (f 3 3) 44))
//@pbe (constraint (= (f 4 2) 45))

// return add(complex_one(x), complex_two(y))
// x + 2x^2 + 3y^2 - y - 1
