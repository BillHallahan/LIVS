// function foo(x) {
//  var y = bar(x) 
//  return bizz(10, y) + " " + bizz(16, x) }
function bar(x) {
 var y = x+4
 return y }
function bizz(base, x) {
 var rounded = Math.round(x)
 var s = rounded.toString(base)
 return (s) }

//@pbe (constraint (= (foo 0) "4 0"))
//@pbe (constraint (= (foo 10) "14 a"))
