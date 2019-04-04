function g ( x ) {
if ( x.length > 3) {
  return x
    .filter ( c => c == c.toLowerCase () )
    .length;
  }
}

//@pbe (constraint (= (f "hello") 4))
//@pbe (constraint (= (f "livs") 3))