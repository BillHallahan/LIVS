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

function f824f(x_0, x_1, x_2)
{
	return mult(x_2, x_2);
}

function f573f(x_0, x_1)
{
	return add(f824f(x_0, x_0, x_1), len(x_0));
}

function f191f(x_0, x_1, x_2)
{
	return f824f(concat(x_2, x_2), x_1, len(x_1));
}

function f628f(x_0, x_1, x_2)
{
	return toStr(add(x_1, x_0));
}

function f49f(x_0, x_1)
{
	return mult(mult(x_0, x_1), x_0);
}

function f347f(x_0)
{
	return len(toStr(x_0));
}

function f981f(x_0, x_1, x_2)
{
	return add(f347f(x_0), add(x_2, x_2));
}

function f124f(x_0, x_1)
{
	return f573f(beforeAfter(x_0), f573f(x_0, x_1));
}

//@pbe (constraint (= (f331f "asdf" 8) 262144))
//@pbe (constraint (= (f331f "ab cd" 10) 1000000))