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
    return mult(f(n, n), n);
}

//@pbe (constraint (= (f 2 2) 32))
//@pbe (constraint (= (f 2 3) 108))
//@pbe (constraint (= (f 3 2) 72))
//@pbe (constraint (= (f 3 3) 243))
//@pbe (constraint (= (f 4 4) 1024))

//@pbe (constraint (= (g 3) 729))
//@pbe (constraint (= (g 4) 4096))
