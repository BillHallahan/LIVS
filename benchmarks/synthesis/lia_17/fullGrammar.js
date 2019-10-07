function complex_one(x) {
    return x + (x * x * 2) - 3
}

function complex_two(x) {
    return (x * x * 3) - x + 2
}

function add(x, y) {
    return x + y
}

//@pbe (constraint (= (f 0) -1))
//@pbe (constraint (= (f 1) 4))
//@pbe (constraint (= (f 2) 19))
//@pbe (constraint (= (f 3) 44))
//@pbe (constraint (= (f 4) 79))

// return add(complex_one(x), complex_two(x))
// 5x^2 - 1
