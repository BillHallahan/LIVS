function h(x) {
	return x - 1;
}

function g ( x ) {
if ( x.length > 3) {
  return x
    .split('')
    .filter ( c => c == c.toLowerCase ())
    // .filter ( function h(c) { c == c.toLowerCase ()} )
    .join('')
    .length;
  }
}

//@pbe (constraint (= (f "hello") 4))
//@pbe (constraint (= (f "livs") 3))
