function g(x, y) {
  return (x * y) - h(y)
}

function h(x) {
  return (x+2)*x
}

function i(x) {
  return x+(x-2)
}

function f(x, y) {
   //@pbe (constraint (= (f 3 2) -6))
   //@pbe (constraint (= (f 4 7) -41))
   return g(x,y)-i(x)
}

f(3, 2)
f(4, 7)
