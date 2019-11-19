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

function f523f(x_0, x_1)
{
	return f607f(len(x_1), f607f(x_0, x_0));
}

//@pbe (constraint (= (f457f 10 "404" "xyz") 15))
//@pbe (constraint (= (f457f 10 "" "") 6))
//@pbe (constraint (= (f457f -3 "xyz" "ab cd") 15))