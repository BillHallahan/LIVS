function threeEvens(x){ 
  if((x % 2) == 0){ return [x, x+2, x+4] } 
  else { return [x+1, x+3, x+5] } } 
function threeOdds(x){ 
  if((x % 2) == 0){ return [x+1, x+3, x+5] } 
  else { return [x, x+2, x+4] } } 
//function sumArrays(x,y){ 
// evens = threeEvens(x) 
//  odds = threeOdds(y) 
//  return (evens[0] + evens[1] + evens[2] + odds[0] + odds[1] + odds[2]) } 

//@pbe (constraint (= (sumArrays 1 2) "27")) 
//@pbe (constraint (= (sumArrays 4 7) "45"))
