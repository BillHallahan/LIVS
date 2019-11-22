// function testFunc(a, b, c, d){
//   var x = numberAdder(a, b);
//   var y = numberMultiplier(c, d);
//   return( x+ y); }
function numberAdder(num1, num2) {
  var aa = num1;
  var bb = num2;
  var cc = aa + bb;
  return cc;
}
function numberMultiplier(num3, num4) {
  var gg = num3;
  var hh = num4;
  var jj = num3*num4;
  return jj;
}

//@pbe (constraint (= (testFunc 1 2 3 4) 15))
//@pbe (constraint (= (testFunc 2 3 4 5) 25))
