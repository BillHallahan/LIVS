function add(m, n) {
  return m + n;
}

function f(n) {
    return add(add(n, n), n);
}

function g(x) {
    return f(f(x))
}

//@pbe (constraint (= (f 2) 8))

//@pbe (constraint (= (g 2) 32))

// Correct function
// function f(n) {
//     return (add((add(n, n)), (n + n) ))}
// }
