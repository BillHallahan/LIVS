function firstWord(word) {
  return word.substring(0, word.indexOf(" ",0));
}

function replaceAll(target, search, replace) {
  return target.split(search).join(replace);
//  return target.replace(new RegExp(search, 'g'), replace);

}

function f() {
  //@pbe (constraint (= (f "Hello World Hello") "Hey World Hey"))
  //@pbe (constraint (= (f "Hello Moon") "Hey Moon"))
}
