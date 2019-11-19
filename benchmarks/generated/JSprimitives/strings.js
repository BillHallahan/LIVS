// @type: 111
function concat(x_0, x_1) {
    return x_0 + x_1;
}

// @type: 11
function len(x_0) {
    return x_0.length + "";
}

// @type: 11
function beforeAfter(x_0) {
    return 'B' + x_0 + 'A';
}

// @type: 11
function lastLetter(x_0) {
    if (x_0.length > 0) { return x_0.slice(-1); } else { return ''; }
}

// @type: 11
function firstWord(x_0) {
    return x_0.substring(0, x_0.indexOf(" "));
}

// @type: 1111
function rep(x_0, x_1, x_2) {
    return x_0.replace(x_1, x_2);
}
