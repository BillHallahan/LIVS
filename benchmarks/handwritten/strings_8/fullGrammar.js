function firstWord(word) {
    return word.substring(0, word.indexOf(" ",0));
}

function replaceAll(target, search, replace) {
    return target.split(search).join(replace);
}

function swap(target) {
    return target.split(" ")[1] + " " + target.split(" ")[0];
}

//@pbe (constraint (= (f "friend" "Hello World") "Hello friend"))
//@pbe (constraint (= (f "friend" "Hi World") "Hi friend"))
//@pbe (constraint (= (f "chum" "Hi World") "Hi chum"))
//@pbe (constraint (= (f "chum" "Hello World") "Hello chum"))
