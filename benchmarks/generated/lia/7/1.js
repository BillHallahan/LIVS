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

function f111f(x_0, x_1, x_2)
{
	return add(add(x_2, x_0), x_1);
}

//@pbe (constraint (= (f138f 8) 15))
//@pbe (constraint (= (f138f -1) -3))