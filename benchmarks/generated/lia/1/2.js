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

function f53f(x_0, x_1)
{
	return double(x_0);
}

function f355f(x_0)
{
	return add(x_0, subtract(x_0, x_0));
}

//@pbe (constraint (= (f112f 3 8 7) 7))
//@pbe (constraint (= (f112f -2 7 6) 6))