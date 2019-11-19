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

function f457f(x_0, x_1, x_2)
{
	return f730f(mult(x_0, x_0), x_0, beforeAfter(x_1));
}

function f38f(x_0, x_1, x_2)
{
	return add(f339f(x_2, x_0), f457f(x_0, x_2, x_2));
}

function f787f(x_0, x_1, x_2)
{
	return len(toStr(x_0));
}

//@pbe (constraint (= (f938f 1) 2))
//@pbe (constraint (= (f938f -5) 1))
//@pbe (constraint (= (f938f 4) 2))
//@pbe (constraint (= (f938f 10) 2))
//@pbe (constraint (= (f938f 1) 2))