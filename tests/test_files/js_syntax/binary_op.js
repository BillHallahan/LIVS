function add(m, n) {
  return m + n;
}

function sub(m, n) {
    return m - n;
}

function mult(m, n) {
    return m * n;
}

function f(n, m) {
    return n + m * n;
}

//@pbe (constraint (= (f 2 3) 5))
//@pbe (constraint (= (f 4 5) 19))

// Correct function
// function f(n, m) {
//     return n + m * n - m;
// }
