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

//@pbe (constraint (= (f 2) 6))

//@pbe (constraint (= (g 2) 32))

// Correct function
// function f(n) {
//     return (add(n, (n + n) ))
// }
