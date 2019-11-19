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

function f746f(x_0, x_1)
{
	return increment(add(x_1, x_0));
}

function f595f(x_0)
{
	return add(f848f(x_0), decrement(x_0));
}

//@pbe (constraint (= (f828f 0 -1 -1) 2))
//@pbe (constraint (= (f828f 3 -4 -3) -4))
//@pbe (constraint (= (f828f 9 2 2) 17))