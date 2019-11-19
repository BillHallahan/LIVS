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

//@pbe (constraint (= (f915f -3 4) -52))
//@pbe (constraint (= (f915f 8 8) 1026))