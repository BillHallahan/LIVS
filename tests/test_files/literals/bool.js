function and(x, y) {
    return x && y;
}

function convert(x) {
    if(x) {
        return 1;
    }
    else {
        return 0;
    }
}

function f(x) {
    return convert(true);
}

//@pbe (constraint (= (f 3) 1))
//@pbe (constraint (= (f 5) 1))
//@pbe (constraint (= (f 0) 0))

// Correct function
// function f(n) {
//     return convert(x)
// }
