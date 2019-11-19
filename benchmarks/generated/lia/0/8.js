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

function f0f(x_0, x_1)
{
	return mult(add(x_1, x_0), mult(x_1, x_0));
}

function f28f(x_0, x_1)
{
	return increment(f0f(x_1, x_1));
}

function f915f(x_0, x_1)
{
	return increment(f28f(x_0, x_0));
}

function f862f(x_0, x_1)
{
	return f0f(decrement(x_1), x_0);
}

function f994f(x_0)
{
	return increment(decrement(x_0));
}

function f850f(x_0, x_1)
{
	return decrement(f0f(x_0, x_0));
}

function f61f(x_0)
{
	return f28f(f994f(x_0), mult(x_0, x_0));
}

function f887f(x_0, x_1)
{
	return decrement(increment(x_1));
}

//@pbe (constraint (= (f757f -2 -5) -14))
//@pbe (constraint (= (f757f -3 -4) -52))
//@pbe (constraint (= (f757f -5 9) -248))
//@pbe (constraint (= (f757f 9 3) 1460))
//@pbe (constraint (= (f757f 9 -5) 1460))