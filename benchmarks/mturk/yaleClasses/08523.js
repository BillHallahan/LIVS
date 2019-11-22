//function comp(x) { 
//  var s = multNine(x) 
//  var q = subSix(s) 
//  return q + 1 } 
function multNine(x) { 
  var y = x * 9 
  return y } 
function subSix(x) { 
  var w = Math.round(((7 * x) - x) / 6) 
  return x * w } 

//@pbe (constraint (= (comp 3) 22)) 
//@pbe (constraint (= (comp 0) -5)) 
//@pbe (constraint (= (comp -1) -14))
