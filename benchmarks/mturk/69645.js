function sumTwoNumbers(a,b){ 
  const c = a + b ; 
  return c ; } 
function multiplyByTwo(x){ 
  const y = x*2 ; 
  return y ; } 
function performCalculations(x,y,z ){ 
  const j = sumTwoNumbers(x,y) 
  const k = multiplyByTwo(z); 
  return (k+j); } 

// @pbe (constraint (=(performCalculations 1 2 3) 9 ) 
// @pbe (constraint (=(performCalculations 2 4 6) 18 )
