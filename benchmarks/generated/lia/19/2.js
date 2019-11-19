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

function f480f(x_0, x_1, x_2)
{
	return increment(decrement(x_1));
}

function f368f(x_0, x_1, x_2)
{
	return subtract(increment(x_0), double(x_0));
}

//@pbe (constraint (= (f550f -3 7) 3))
//@pbe (constraint (= (f550f -2 1) 2))
//@pbe (constraint (= (f550f -1 2) 1))