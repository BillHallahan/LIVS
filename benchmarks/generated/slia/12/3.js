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

//@pbe (constraint (= (f730f 2 8 "404") 9))
//@pbe (constraint (= (f730f 6 2 "xyz") 9))
//@pbe (constraint (= (f730f 2 1 "ab cd") 15))
//@pbe (constraint (= (f730f 5 2 "vvvvv") 15))
//@pbe (constraint (= (f730f 2 6 "vvvvv") 15))