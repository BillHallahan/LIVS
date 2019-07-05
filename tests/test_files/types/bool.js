function and(x, y) {
    if(x) {
        if(y) {
            return true;
        }
    }
    return false;
}

function or(x, y) {
    if(x) {
        return true;
    }
    if(y) {
        return true;
    }
    return false;
}

function f(x, y) {
    return or(x, y);
}

//@pbe (constraint (= (f true true) true))
//@pbe (constraint (= (f true false) false))
//@pbe (constraint (= (f false false) false))

// Correct function
// function f(x, y) {
//     return and(x, y);
// }
