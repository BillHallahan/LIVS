function convert(s) {
    return s.length;
}

function add(m, n) {
  return m + n;
}

function f(n) {
    return add(convert("hello"), n);
}

//@pbe (constraint (= (f 3) 11))
//@pbe (constraint (= (f 4) 13))

// Correct function
// function f(n) {
//     return (add(convert("hello"), add(n, n)))
// }
