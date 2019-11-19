function firstWord(word) {
  return word.substring(0, word.indexOf(" ",0));
}

function replaceAll(target, search, replace) {
  return target.split(search).join(replace);
//  return target.replace(new RegExp(search, 'g'), replace);

}

//@pbe (constraint (= (f "Hey" "Hello World Hello") "Hey World Hey"))
//@pbe (constraint (= (f "Hey" "Hello Moon") "Hey Moon"))
