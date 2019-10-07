function addone(x) {
    return x + 1
}

function add(x, y) {
    return x + y
}

function long(a, b, c, d, e, f, g) {
    return a + b + c + d + e + f + g * 2
}

//@pbe (constraint (= (f 1 2 3) 14))
//@pbe (constraint (= (f 3 2 1) 18))
//@pbe (constraint (= (f 1 1 1) 8))
//@pbe (constraint (= (f 2 2 2) 16))
//@pbe (constraint (= (f 2 1 1) 12))

// return long(x, y, z, x, y, z, x)
// 4x + 2y + 2z
