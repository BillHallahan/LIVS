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

function f998f(x_0)
{
	return add(x_0, mult(x_0, x_0));
}

function f351f(x_0, x_1, x_2)
{
	return beforeAfter(concat(x_0, x_0));
}

function f532f(x_0, x_1)
{
	return f998f(f998f(x_0));
}

function f543f(x_0, x_1, x_2)
{
	return len(concat(x_0, x_0));
}

function f349f(x_0, x_1, x_2)
{
	return concat(beforeAfter(x_1), concat(x_1, x_1));
}

function f958f(x_0, x_1)
{
	return beforeAfter(beforeAfter(x_0));
}

function f317f(x_0, x_1, x_2)
{
	return f958f(toStr(x_2), len(x_1));
}

function f694f(x_0, x_1)
{
	return len(concat(x_0, x_0));
}

function f85f(x_0, x_1, x_2)
{
	return f351f(x_2, x_1, add(x_1, x_1));
}

//@pbe (constraint (= (f832f "hello world" 5 8) 26))
//@pbe (constraint (= (f832f "404" 8 3) 10))