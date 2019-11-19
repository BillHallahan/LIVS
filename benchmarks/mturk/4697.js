// function sumrands(x) {
//  var a = gennum(x)
//  var b = genhun(x)
//  var c = a+b
//  return c }
function gennum(x) {
 var d = Math.floor((Math.random() * 10) + x)
 return d }
function genhun(x){
 var e = Math.floor((Math.random() * 100) + x)
 return e }

//between 23-128 and 12-118 repsectively

//@pbe (constraint (= (f 10) 23))
//@pbe (constraint (= (f 5) 13))
