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

function f753f(x_0, x_1, x_2)
{
	return len(x_1);
}

function f566f(x_0)
{
	return beforeAfter(concat(x_0, x_0));
}

function f624f(x_0, x_1, x_2)
{
	return beforeAfter(x_0);
}

function f581f(x_0, x_1, x_2)
{
	return f624f(beforeAfter(x_1), x_0, mult(x_2, x_2));
}

function f415f(x_0, x_1, x_2)
{
	return add(add(x_1, x_1), add(x_1, x_1));
}

function f765f(x_0, x_1, x_2)
{
	return add(add(x_2, x_2), f753f(x_1, x_1, x_2));
}

function f850f(x_0, x_1)
{
	return f624f(toStr(x_0), x_1, f415f(x_1, x_0, x_1));
}

function f700f(x_0)
{
	return beforeAfter(beforeAfter(x_0));
}

//@pbe (constraint (= (f497f 6 "ab cd" "mno pqr st") "12"))
//@pbe (constraint (= (f497f 3 "vvvvv" "hello world") "6"))