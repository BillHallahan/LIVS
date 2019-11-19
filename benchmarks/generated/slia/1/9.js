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
	return (x_0 + 10) + "";
}

function beforeAfter(x_0)
{
	return 'B' + x_0 + 'A';
}

function f530f(x_0, x_1, x_2)
{
	return mult(mult(x_1, x_1), mult(x_1, x_1));
}

function f503f(x_0, x_1)
{
	return concat(x_1, beforeAfter(x_1));
}

function f609f(x_0, x_1)
{
	return f530f(beforeAfter(x_1), f530f(x_1, x_0, x_1), f503f(x_0, x_1));
}

function f57f(x_0, x_1)
{
	return len(f503f(x_1, x_0));
}

function f688f(x_0, x_1)
{
	return concat(beforeAfter(x_1), f503f(x_0, x_1));
}

function f953f(x_0, x_1, x_2)
{
	return f530f(x_1, len(x_1), f503f(x_0, x_1));
}

function f73f(x_0, x_1)
{
	return len(beforeAfter(x_0));
}

function f166f(x_0, x_1, x_2)
{
	return beforeAfter(beforeAfter(x_2));
}

function f707f(x_0, x_1, x_2)
{
	return f57f(concat(x_1, x_1), mult(x_0, x_2));
}

//@pbe (constraint (= (f103f "ab cd" 5 3) 42))
//@pbe (constraint (= (f103f "vvvvv" 2 -3) 42))
//@pbe (constraint (= (f103f "xyz" -4 7) 26))
//@pbe (constraint (= (f103f "404" -2 8) 26))
//@pbe (constraint (= (f103f "404" 1 6) 26))