function add(m, n) {
  return m + n;
}

function f(n, m) {
    return add(add(n, m), n);
}

function g(a) {
    return add(a, a);
}

// Repair target
//@pbe (constraint (= (f 2 3) 10))
//@pbe (constraint (= (f 10 11) 42))

//@pbe (constraint (= (g 4) 8))

//@pbe (constraint (= (add 2 3) 5))
//@pbe (constraint (= (add 4 5) 9))

// Correct function
// function f(n, m) {
//     return (add(add(n, m), add(n, m)))
// }
