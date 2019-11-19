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

//@pbe (constraint (= (f884f 8 1 -2) 51))
//@pbe (constraint (= (f884f 8 6 5) 51))
//@pbe (constraint (= (f884f -4 -5 9) -21))
//@pbe (constraint (= (f884f 9 10 5) 57))
//@pbe (constraint (= (f884f 10 2 1) 63))