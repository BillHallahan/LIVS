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

//@pbe (constraint (= (f700f "vvvvv") "BBvvvvvAA"))
//@pbe (constraint (= (f700f "mno pqr st") "BBmno pqr stAA"))
//@pbe (constraint (= (f700f "hello world") "BBhello worldAA"))
//@pbe (constraint (= (f700f "404") "BB404AA"))