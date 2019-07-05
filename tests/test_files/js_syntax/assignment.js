function add(m, n) {
  return m + n;
}

// returns 4m + 3n
function f(n, m) {
    var x = add(n, m);
    y = add(x, m);
    let z = add(y, n);
    return add(z, y);
}

//@pbe (constraint (= (f 2 3) 15))
//@pbe (constraint (= (f 4 5) 27))

// Correct function
// function f(n, m) {
//     var x = add(n, m);
//     y = add(x, m);
//     let z = add(y, n);
//     return (add(x, y))
// }
