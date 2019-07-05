function add(m, n) {
  return m + n;
}

function f(n) {
    return add(n, add(n, n));
}

//@pbe (constraint (= (f 2.5) 5.0))
//@pbe (constraint (= (f 3.0) 6.0))

// Correct function
// function f(n) {
//     return (add(n, n))
// }
