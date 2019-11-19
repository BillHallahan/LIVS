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

function f828f(x_0, x_1, x_2)
{
	return subtract(mult(x_0, x_2), f892f(x_1));
}

function f194f(x_0, x_1, x_2)
{
	return f828f(add(x_2, x_1), subtract(x_2, x_0), x_2);
}

function f884f(x_0, x_1, x_2)
{
	return f595f(f848f(x_0));
}

function f304f(x_0, x_1)
{
	return f828f(f828f(x_0, x_1, x_0), subtract(x_0, x_0), decrement(x_0));
}

//@pbe (constraint (= (f999f 1 2) 3))
//@pbe (constraint (= (f999f 1 1) 2))
//@pbe (constraint (= (f999f 6 6) 72))