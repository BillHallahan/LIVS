// @type: 000
function add(x_0, x_1) {
    return x_0 + x_1;
}

// @type: 000
function mult(x_0, x_1) {
    return x_0 * x_1;
}

// @type: 111
function concat(x_0, x_1) {
    return x_0 + x_1;
}

// @type: 00
function increment(x_0) {
    return x_0 + 1;
}

// @type: 10
function len(x_0) {
    return x_0.length;
}

// @type: 01
function toStr(x_0) {
    return x_0 + "";
}

// @type: 011
function appendNum(x_0, x_1) {
    return x_1 + x_0;
}

// @type: 101
function rptStr(x_0, x_1) {
    if(x_1 <= 5) { return x_0.repeat(x_1); } else { return x_0.repeat(5); }
}
