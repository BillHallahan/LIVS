// function halfAddDouble(x) {
//  h = half(x)
//  d = double(x)
//  return (h + d) }
function half(x) {
 var val = x;
 return val * 2;
}

function double(x) {
 var val = x;
 return (1 / half(val));
}

//@pbe (constraint (= (f 1) 2.5))
//@pbe (constraint (= (f 2) 4.25))
