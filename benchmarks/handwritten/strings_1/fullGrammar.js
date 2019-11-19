function firstWord(word) {
  return word.substring(0, word.indexOf(" "));
}

function rep(s1, s2, s3) { return s1.replace(s2, s3) }

//@pbe (constraint (= (f "Hey" "Hello World") "Hey World"))
//@pbe (constraint (= (f "Hey" "Hello Moon") "Hey Moon"))
