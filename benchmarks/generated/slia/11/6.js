function add(x_0, x_1)
{
	return x_0 + x_1;
}

function mult(x_0, x_1)
{
	return x_0 * x_1;
}

function concat(x_0, x_1)
{
	return x_0 + x_1;
}

function len(x_0)
{
	return x_0.length;
}

function toStr(x_0)
{
	return x_0 + "";
}

function beforeAfter(x_0)
{
	return 'B' + x_0 + 'A';
}

function f612f(x_0, x_1)
{
	return mult(len(x_1), mult(x_0, x_0));
}

function f610f(x_0, x_1)
{
	return f612f(add(x_0, x_0), toStr(x_0));
}

function f338f(x_0, x_1)
{
	return add(mult(x_1, x_1), mult(x_1, x_1));
}

function f774f(x_0, x_1, x_2)
{
	return mult(f610f(x_2, x_0), f610f(x_2, x_0));
}

function f116f(x_0, x_1, x_2)
{
	return len(toStr(x_1));
}

function f122f(x_0, x_1, x_2)
{
	return beforeAfter(toStr(x_2));
}

//@pbe (constraint (= (f419f 9 "ab cd" 3) 10935))
//@pbe (constraint (= (f419f 9 "mno pqr st" 0) 0))
//@pbe (constraint (= (f419f 4 "mno pqr st" 10) 6400))
//@pbe (constraint (= (f419f 8 "asdf" 2) 4096))
//@pbe (constraint (= (f419f 6 "mno pqr st" 9) 19440))