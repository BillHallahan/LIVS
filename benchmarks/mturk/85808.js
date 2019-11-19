function thesecond(x) {
  var y = x+6
  var z = y+8
  return z }
function thethird(z, x) {
  var v = Math.floor(Math.random() * z) +x;
  var w = v*2
  return w }
// function themain(x) {
//   var z = thesecond(x)
//   return thesecond(z) + thethird(z, x) }

//@pbe (constraint (= (themain 2) 60))
//@pbe (constraint (= (themain 10) 64))
