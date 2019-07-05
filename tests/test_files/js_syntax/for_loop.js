function add(x, y) {
    return x + y;
}

function less(x, y) {
    return x < y;
}

function greater(x, y) {
    return x > y;
}

function leq(x, y) {
    return x <= y;
}

function geq(x, y) {
    return x >= y;
}

function f(x) {
    var sum = 0;
    for(var i = 1; i < x; i++)
    {
        sum += i;
    }
    return sum;
}

//@pbe (constraint (= (f 5) 15))
//@pbe (constraint (= (f 1) 1))
//@pbe (constraint (= (f 7) 28))
//@pbe (constraint (= (f 3) 6))
//@pbe (constraint (= (f 10) 55))

// Correct function
// function f(x) {
//     var sum = 0;
//     for(var i = 1; i <= x; i++)
//     {
//         sum += i;
//     }
//     return sum;
// }
