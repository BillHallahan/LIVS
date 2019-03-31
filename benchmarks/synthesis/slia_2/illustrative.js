function containsNum(p) {
  return /\d/.test(p);
}

function noNum(p) {
  return "Your password must have a number"
}

//read from a database to check if a password has been used
function usedBefore(user, password) {
  const fs = require('fs');
  var rawdata = fs.readFileSync(user+'.json');  
  var oldPasswords = JSON.parse(rawdata);  
  return password.indexOf(oldPasswords) >= 0

}

function usedBeforeError() {
  return "You already used a version of this password"
}

function checkBadPassword(u,p) {
  if (usedBefore(u.toLowerCase(),p)) {
    return usedBeforeError();
  }
  else if (!containsNum(p)){
    return noNum();
  }
  else {
    return false;
  }
}


//@pbe (constraint (= (checkBadPassword "mark" "mark")  "Your password must have a number")
//@pbe (constraint (= (checkBadPassword "mark" "mark1") "You already used a version of this password")
//@pbe (constraint (= (checkBadPassword "mark" "mark2") false)
