function and(x, y) {
    if(x) {
        if(y) {
            return true;
        }
    }
    return false;
}

function convert(x) {
    if(x) {
        return 1;
    }
    else {
        return 0;
    }
}

function greaterThree(x) {
    return x > 3;
}

function lessFive(x) {
    return x < 5;
}

function f(x) {
    return convert(and(greaterThree(x), true));
}

//@pbe (constraint (= (f 2) 50))
//@pbe (constraint (= (f 4) 100))
//@pbe (constraint (= (f 7) 50))

// Correct function
// function f(n) {
//     return convert(and(greaterThree(x), lessFive(x)))
// }
