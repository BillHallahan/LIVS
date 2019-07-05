function less(x, y) {
    return x < y;
}

function greater(x, y) {
    return x > y;
}

function f(x, y, z) {
    if(x > y)
    {
        return true;
    }
    else if(x < z)
    {
        return true;
    }
    else
    {
        return false;
    }
}

//@pbe (constraint (= (f 5 6 7) false))
//@pbe (constraint (= (f 1 5 5) false))
//@pbe (constraint (= (f 3 2 4) true))
//@pbe (constraint (= (f 10 4 2) true))
//@pbe (constraint (= (f 9 1 1) true))

// Correct function
// function f(x, y, z) {
//     if(x > y)
//     {
//         return true;
//     }
//     else if(x > z)
//     {
//         return true;
//     }
//     else
//     {
//         return false;
//     }
// }
