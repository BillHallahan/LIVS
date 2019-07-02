function add(m, n) {
  return m + n;
}

function f(n) {
    return add(add(n, n), n);
}

//@pbe (constraint (= (f 2) 8))
//@pbe (constraint (= (f 3) 12))

// Correct function
// function f(n) {
//     return (add(add(n, n), add(n, n)))
// }
