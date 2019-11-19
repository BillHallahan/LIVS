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

function f1f(x_0)
{
	return subtract(increment(x_0), add(x_0, x_0));
}

//@pbe (constraint (= (f100f 5) -5))
//@pbe (constraint (= (f100f 3) -3))