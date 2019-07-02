function add(m, n) {
  return m + n;
}

function f(n, m) {
    return add(add(n, m), n);
}

//@pbe (constraint (= (f 2 3) 10))
//@pbe (constraint (= (f 10 11) 42))

// Correct function
// function f(n, m) {
//     return (add(add(n, m), add(n, m)))
// }
