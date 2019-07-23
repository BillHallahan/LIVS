function mult(m, n) {
  return m * n;
}

function f(n) {
    return mult(n, n);
}

function h(y) {
    return mult(y, f(y));
}

function g(a, b) {
    return mult(f(a), f(b));
}

function k(z) {
    return mult(z, h(z));
}

//@pbe (constraint (= (f 2) 8))

//@pbe (constraint (= (h 3) 81))

//@pbe (constraint (= (g 2 3) 216))

//@pbe (constraint (= (k 2) 32))

// Correct function
// function f(n) {
//     return (mult(n, (mult(n, n))))
// }
