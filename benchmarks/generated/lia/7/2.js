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

function f138f(x_0)
{
	return decrement(double(x_0));
}

//@pbe (constraint (= (f522f -1 8) 10))
//@pbe (constraint (= (f522f 0 5) 6))
//@pbe (constraint (= (f522f -5 6) 12))
//@pbe (constraint (= (f522f 3 6) 4))