function g ( x ) {
if ( x.length >3) {
  return x
    .filter ( c = > c == c.toLowerCase () )
    .length;
  }
}

function f ( x ) {
  //@pbe (constraint (= (f "hello") 4))
  //@pbe (constraint (= (f "livs") 3))
}
