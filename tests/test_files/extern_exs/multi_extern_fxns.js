function add(m, n) {
  return m + n;
}

function f(n) {
    return add(n, n);
}

function h(y) {
    return add(y, f(y));
}

function g(x) {
    return h(h(x));
}

function k(z) {
    return f(f(z))
}

//@pbe (constraint (= (f 2) 6))

//@pbe (constraint (= (h 3) 12))

//@pbe (constraint (= (g 2)) 32))

//@pbe (constraint (= (k 5) 45))

// Correct function
// function f(n) {
//     return (add(add(n, n), n))
// }
