function add(x_0, x_1)
{
	return x_0 + x_1;
}

function mult(x_0, x_1)
{
	return x_0 * x_1;
}

function increment(x_0)
{
	return x_0 + 1;
}

function decrement(x_0)
{
	return x_0 - 1;
}

function subtract(x_0, x_1)
{
	return x_0 - x_1;
}

function double(x_0)
{
	return x_0 * 2;
}

function f890f(x_0, x_1)
{
	return subtract(add(x_0, x_0), mult(x_1, x_0));
}

function f387f(x_0)
{
	return increment(decrement(x_0));
}

function f461f(x_0)
{
	return f387f(increment(x_0));
}

function f555f(x_0)
{
	return f387f(f890f(x_0, x_0));
}

function f396f(x_0, x_1, x_2)
{
	return f461f(double(x_1));
}

function f119f(x_0, x_1, x_2)
{
	return mult(f890f(x_0, x_1), f555f(x_0));
}

function f940f(x_0, x_1, x_2)
{
	return increment(double(x_1));
}

function f711f(x_0)
{
	return f396f(add(x_0, x_0), f940f(x_0, x_0, x_0), mult(x_0, x_0));
}

//@pbe (constraint (= (f189f 8) -95))
//@pbe (constraint (= (f189f 3) -5))
//@pbe (constraint (= (f189f 10) -159))
//@pbe (constraint (= (f189f 8) -95))
//@pbe (constraint (= (f189f 3) -5))