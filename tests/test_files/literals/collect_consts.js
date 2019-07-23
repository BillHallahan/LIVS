function mult(m, n) {
    return m * n;
}

function add(m, n) {
  return m + n;
}

function f(n) {
    return mult(2, add(n, n));
}

//@pbe (constraint (= (f 2) 8))
//@pbe (constraint (= (f 3) 15))
//@pbe (constraint (= (f 4) 24))
//@pbe (constraint (= (f 5) 35))

// Correct function
// function f(n) {
//     return (mult(n, add(n, 2)))
// }
