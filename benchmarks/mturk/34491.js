function addMinAndMax(x) { 
  if (x.length == 0) 
    { return 0 } 
  min = getMin(x) 
  max = getMax(x) 
  return min + max } 
function getMin(x) { 
  arr = x 
  return Math.min.apply(null, arr) } 
function getMax(x) { 
  arr = x 
  return Math.max.apply(null, arr) } 

//@pbe (constraint (= (addMinAndMax [1,2,3]) 4)) 
//@pbe (constraint (= (addMinAndMax [1,2,-3]) -1))
