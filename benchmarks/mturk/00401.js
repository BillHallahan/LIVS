function getFirstAppendLast(s) { 
  if (s == "") 
   { return ""} 
  first = getFirst(s) 
  last = getLast(s) 
  return first + last } 
function getFirst(s) { 
  c = s[0] 
  return c } 
function getLast(s) { 
  c = s[s.length - 1] 
  return c } 

//@pbe (constraint (= (getFirstAppendLast "united states") "us")) 
//@pbe (constraint (= (getFirstAppendLast "china") "ca"))
