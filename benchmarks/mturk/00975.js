// function testFunc(a, b, c, d){
//   var x = numberAdder(a, b);
//   var y = numberMultiplier(c, d);
//   return( x+ y); }
function numberAdder(Num1, Num2) {
  var aa = Num1;
  var bb = Num2
  var cc = aa + bb;
  return cc; }
function numberMultiplier(Num3, Num4) {
  var gg = Num3;
  var hh = Num4;
  var jj = Num3*Num4;
return jj; }

//@pbe (constraint (= testFunc (1 2 3 4) 15))
//@pbe (constraint (= testFunc (2 3 4 5) 25))
