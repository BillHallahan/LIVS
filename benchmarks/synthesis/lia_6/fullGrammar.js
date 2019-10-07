function g(x, y) {
  return (x * y) - h(y)
}

function h(x) {
  return (x + 2) * x
}

function i(x) {
  return x + (x - 2)
}

function sub(x, y) {
  return x - y
}

function a(x, y) {
    return x + y + 1
}

function b(x, y) {
    return x + y + 2
}

function c(x, y) {
    return x + y + 3
}

function d(x, y) {
    return (x + y) * 2
}

function e(x, y) {
    return (x + y) * 3
}

function j(x, y) {
    return (x + y) * 4
}

function k(x, y) {
    return (x + y) * 5
}

function l(x, y) {
    return (x + y) * 6
}

function m(x, y) {
    return x * y + 1
}

function n(x, y) {
    return x * y + 2
}

function o(x, y) {
    return x * y + 3
}

function aa(x) {
    return a(x, x) - 1
}

function bb(x) {
    return b(x, x) + 1
}

function cc(x) {
    return c(x, x) - 1
}

function dd(x) {
    return d(x, x) + 1
}

function ee(x) {
    return e(x, x) - 1
}

function jj(x) {
    return j(x, x) + 1
}

function kk(x) {
    return k(x, x) - 1
}

function ll(x) {
    return l(x, x) + 1
}

function mm(x) {
    return m(x, x) + 1
}

function nn(x) {
    return n(x, x) - 1
}

function oo(x) {
    return o(x, x) + 1
}

//@pbe (constraint (= (f 0 0) 8))
//@pbe (constraint (= (f 1 1) 26))
//@pbe (constraint (= (f 1 2) 38))
//@pbe (constraint (= (f 2 1) 39))
//@pbe (constraint (= (f 2 2) 52))
//@pbe (constraint (= (f 3 3) 86))

//return j(nn(x), dd(y)) + g(x, y)
// 4x^2 + 14y + 8 + xy - y^2
