function misc(n) {
    return 2 * n * n * n;
}

function add(m, n) {
  return m + n;
}

function f(n) {
    return add(n, n);
}

//@pbe (constraint (= (f 2) 6))
//@pbe (constraint (= (f 3) 8))
//@pbe (constraint (= (f 4) 10))

// Correct function
// function f(n) {
//     return (add(2, add(n, n)))
// }
