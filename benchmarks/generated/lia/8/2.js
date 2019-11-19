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

function f131f(x_0, x_1, x_2)
{
	return add(add(x_0, x_0), mult(x_1, x_0));
}

function f736f(x_0)
{
	return add(mult(x_0, x_0), f131f(x_0, x_0, x_0));
}

//@pbe (constraint (= (f962f -1 -1) 2))
//@pbe (constraint (= (f962f -5 8) 10))