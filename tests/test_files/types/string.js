function return2() {
    return 2;
}

function subs(s, i, j) {
    return s.substring(i, j);
}

function f(s, n) {
    return subs(s, 0, 3);
}

//@pbe (constraint (= (f "hellooo") "he"))
//@pbe (constraint (= (f "world") "wo"))
//@pbe (constraint (= (f "test") "te"))

// Correct function
// function f(s) {
//     return (subs(s, 0, 2))
// }
