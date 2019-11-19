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

//@pbe (constraint (= (f194f 9 10 1) 20))
//@pbe (constraint (= (f194f -3 -1 4) 6))
//@pbe (constraint (= (f194f 6 -3 1) 4))
//@pbe (constraint (= (f194f 8 3 -5) 24))
//@pbe (constraint (= (f194f -2 10 1) 9))