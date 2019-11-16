function multiply(num1, num2) { 
  return num1 * num2; }
 multiply(); // Returns 60 
function getScore(name, num1, num2) { 
  function add() { return name + ' scored ' + multiply(num1,num2); } 
   return add(); } 

//@pbe (constraint (= (getScore "Chamahk" 20 3) "Chamahk scored 60"))
