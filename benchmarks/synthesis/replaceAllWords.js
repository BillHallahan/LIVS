function firstWord(word) {
  return word.substring(0, word.indexOf(0));
}

function replaceAll(target, search, replacement) {
  return target.split(search).join(replacement);
}

function f() {
  //@pbe (constraint (= (f "Hello World") "Hey World Hey"))
  //@pbe (constraint (= (f "Hello Moon") "Hey Moon"))
}
