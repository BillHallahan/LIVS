// function results(x) {
//  if (x > 0)
//    return x + " " + plusOne(x) + " " + plusTwo(x)
//  else
//    return 0 }
function plusOne(x) {
 var y = x+1;
 return y;
}

function plusTwo(x) {
 var y = x+2;
 return y;
}


//@pbe (constraint (= (results 1) "1 2 3"))
//@pbe (constraint (= (results 19) "19 20 21"))
//@pbe (constraint (= (results -1) 0))
