function and(x, y) {
    return x && y;
}

function or(x, y) {
    return x || y;
}

function f(x, y, z) {
    return (x && y);
}

//@pbe (constraint (= (f true true false) true))
//@pbe (constraint (= (f true false true) true))
//@pbe (constraint (= (f true false false) false))
//@pbe (constraint (= (f false false false) false))
//@pbe (constraint (= (f false true true) false))

// Correct function
// function f(x, y, z) {
//     return x && (y || z);
// }
