function helper1(str) { 
  return str.toUpperCase(); } 
function helper2(str, num) { 
  let result = ""; 
  for(let i = 0; i < num; i++) { 
    result += str; } 
  return result; } 
function loud(str, num) { 
  return helper2(helper1(str), num); } 

//@pbe (constraint (= (loud "a" 2) "AA")) 
//@pbe (constraint (= (loud "hELLo" 3) "HELLOHELLOHELLO")) 
//@pbe (constraint (= (loud "empty" 0) ""))
