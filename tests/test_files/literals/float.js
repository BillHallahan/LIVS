function add(m, n) {
  return m + n;
}

function round(n) {
    return Math.round(n);
}

function f(n) {
    return add(round(2.345), n);
}

//@pbe (constraint (= (f 3) 8))
//@pbe (constraint (= (f 4) 10))

// Correct function
// function f(n) {
//     return (add(round(2.345), add(n, n)))
// }
