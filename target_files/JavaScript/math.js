function add(m, n) {
  return m + n;
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

function f(n) {
    return n * quadruple(n);
}

function g(n) {
    return f(n) * square(n);
}

//@pbe (constraint (= (f 2) 32))
//@pbe (constraint (= (f 3) 243))
//@pbe (constraint (= (f 4) 1024))
