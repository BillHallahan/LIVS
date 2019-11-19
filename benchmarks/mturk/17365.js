function square(number) {
  return number * number; }
var square = function(number) {
  return number * number; };
var x = square(4); // x gets the value 16 
var factorial = function fac(n) {
  return n < 2 ? 1 : n * fac(n - 1);
  };

//@pbe (constraint (= (factorial 3) 6))
//@pbe (constraint (= (factorial 4) 24))
