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

function f687f(x_0, x_1)
{
	return subtract(increment(x_1), increment(x_0));
}

function f270f(x_0)
{
	return f687f(double(x_0), increment(x_0));
}

function f469f(x_0, x_1)
{
	return add(mult(x_1, x_1), f270f(x_1));
}

function f414f(x_0)
{
	return f469f(subtract(x_0, x_0), double(x_0));
}

//@pbe (constraint (= (f212f -5) -6))
//@pbe (constraint (= (f212f 4) 3))
//@pbe (constraint (= (f212f -3) -4))
//@pbe (constraint (= (f212f 10) 9))