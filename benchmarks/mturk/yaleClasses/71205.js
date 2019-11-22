// function boss(x) { 
//  var y = Math.clz32(x) 
//  var z = emp1(x,y) 
//  return emp2(x,y,z) } 
function emp1(x,y){ 
  return Math.ceil(x/y); } 
function emp2(x,y,z){ 
  return (x * y) % z } 


//@pbe (constraint (= (boss 2) 0))
