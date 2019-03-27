function g(x, y) {
  return (x * y) - h(y)
}

function h(x) {
  return (x+2)*x
}

//@pbe (constraint (= (f 3 2) -5))
//@pbe (constraint (= (f 4 7) -39))
// return g(x,y)-x

