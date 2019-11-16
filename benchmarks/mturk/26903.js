function findPeri(l,w){ 
  var p = 2 * (l + w) 
  return(p) } 
function findArea(l,w){ 
  var a = l * w 
  return(a) } 
function rectangle(l,w){ 
  var peri = findPeri(l,w) 
  var area = findArea(l,w) 
  return peri + " " + area } 

//@pbe (constraint (= (2 4) "12 8")) 
//@pbe (constraint (= (5 8) "26 40"))
