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

function f607f(x_0, x_1)
{
	return add(x_1, add(x_0, x_0));
}

function f363f(x_0, x_1)
{
	return beforeAfter(concat(x_1, x_1));
}

function f339f(x_0, x_1)
{
	return add(add(x_1, x_1), add(x_1, x_1));
}

function f730f(x_0, x_1, x_2)
{
	return f607f(len(x_2), len(x_2));
}

//@pbe (constraint (= (f523f 0 "xyz") 6))
//@pbe (constraint (= (f523f 2 "mno pqr st") 26))
//@pbe (constraint (= (f523f 0 "hello world") 22))
//@pbe (constraint (= (f523f -3 "") -9))