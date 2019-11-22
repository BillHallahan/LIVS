// function first(x) { 
//  const s = second(x) 
//  const t = third(x) 
//  return (s * t) } 
function second(x) { 
  const y = x * 42 
  return y } 
function third(x) { 
  const y = Math.floor(x / 42) 
  return y } 


//@pbe (constraint (= (first 10) 0)) 
//@pbe (constraint (= (first 50) 2100))
