function add(m, n) {
    return m + n;
}

function f(x) {
    return x;
}

//@pbe (constraint (= (f "hi") "hihi"))
//@pbe (constraint (= (f 3) 6))

// Correct function
// function f(x) {
//     return (add(x, x))
// }
