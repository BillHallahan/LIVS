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

function f184f(x_0, x_1)
{
	return mult(len(x_1), len(x_0));
}

function f399f(x_0, x_1, x_2)
{
	return toStr(add(x_2, x_2));
}

function f115f(x_0, x_1, x_2)
{
	return len(concat(x_2, x_0));
}

function f487f(x_0)
{
	return f184f(concat(x_0, x_0), beforeAfter(x_0));
}

//@pbe (constraint (= (f381f 8 "404") 1))
//@pbe (constraint (= (f381f 5 "xyz") 1))