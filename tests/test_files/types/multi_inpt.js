function add(m, n) {
    return m + n;
}

function subs(s, i, j) {
    return s.substring(i, j);
}

function f(s, n) {
    return subs(s, 0, n);
}

//@pbe (constraint (= (f "hellooo" 3) "helloo"))
//@pbe (constraint (= (f "world" 2) "worl"))
//@pbe (constraint (= (f "test" 2) "test"))

// Correct function
// function f(s, n) {
//     return (subs(s, 0, add(n, n)))
// }
