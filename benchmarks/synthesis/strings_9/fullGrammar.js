function swap(target) {
    return target.split(" ")[1] + " " + target.split(" ")[0];
}

function rev(s) {
    return s.split("").reverse().join("")
}

//@pbe (constraint (= (f "Hello World") "olleH dlroW"))
//@pbe (constraint (= (f "Hi World") "iH dlroW"))
//@pbe (constraint (= (f "Hi Friend") "iH dneirF"))
