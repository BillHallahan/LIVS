function convert(x) {
    if(x) {
        return 100;
    }
    else {
        return 50;
    }
}

function greaterThree(x) {
    return x > 3;
}

function a(x) {
    return x < 5;
}

function f(x) {
    return convert(greaterThree(x));
}

//@pbe (constraint (= (f 2) 50))
//@pbe (constraint (= (f 4) 100))

// Correct function
// function f(n) {
//     return convert(and(greaterThree(x), lessFive(x)))
// }
