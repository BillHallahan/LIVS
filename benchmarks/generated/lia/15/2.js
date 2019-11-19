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

function f892f(x_0)
{
	return decrement(x_0);
}

function f848f(x_0)
{
	return increment(double(x_0));
}

//@pbe (constraint (= (f746f 1 7) 9))
//@pbe (constraint (= (f746f 9 -5) 5))