function add(m, n) {
  return m + n;
}

function mult(m, n) {
    return m * n;
}

function square(n) {
  return n * n;
}

function cube(n) {
  return n * n * n;
}

function quadruple(n) {
    return square(n) * square(n)
}

function f(n, m) {
    return mult(n, mult(n, mult(n, m)));
}

function g(n) {
    return mult(f(n, 2.5), n);
}

// function h(n) {
//     return add(2, n);
// }

//@pbe (constraint (= (h 2) 4))
//@pbe (constraint (= (h 3) 9))
