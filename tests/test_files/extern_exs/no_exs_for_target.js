function add(m, n) {
  return m + n;
}

function f(n, m) {
    return add(n, m);
}

function h(y) {
    return add(y, f(y, y));
}

function g(x) {
    return h(h(x));
}

function k(z) {
    return f(f(z))
}

//@pbe (constraint (= (h 3) 12))

//@pbe (constraint (= (g 2)) 32))

//@pbe (constraint (= (k 5) 45))

// Correct function
// function f(n, m) {
//     return (add(add(n, m), n))
// }
