function add(m, n) {
  return m + n;
}

function round2(n) {
    return 2;
}

function f(n) {
    return add(round2(2.345), n);
}

//@pbe (constraint (= (f 3) 8))
//@pbe (constraint (= (f 4) 10))

// Correct function
// function f(n) {
//     return (add(round(2.345), add(n, n)))
// }
