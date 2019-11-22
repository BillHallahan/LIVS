//function top(num) { 
//  var neg = negate(num) 
//  return (square(num) + "=?=" + square(neg)) } 
function negate(n) { 
  var neg = 0 - n 
  return neg } 
function square(n) { 
  var s = n * n 
  return (s.toString(10)) } 
function x() { return "=?=" }

//@pbe (constraint (= (top 1) "1=?=1")) 
//@pbe (constraint (= (top 5) "25=?=25"))
