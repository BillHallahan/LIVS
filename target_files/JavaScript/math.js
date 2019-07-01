function add(m, n) {
  return m + n;
}

function mult(m, n) {
    return m * n;
}

function square(n) {
  return n * n;
}

function quadruple(n) {
    return square(n) * square(n)
}

function f(n) {
    return mult(mult(n, n), add(n,n));
}
//
// function h(m) {
//     return add(m, f(m));
// }
//
// function g(k) {
//     return mult(h(k), k);
// }

//@pbe (constraint (= (f 2) 16))
//@pbe (constraint (= (f 3) 81))
