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

function f85f(x_0, x_1, x_2)
{
	return mult(decrement(x_2), add(x_0, x_1));
}

function f727f(x_0, x_1)
{
	return increment(x_1);
}

function f625f(x_0, x_1, x_2)
{
	return double(f727f(x_2, x_2));
}

//@pbe (constraint (= (f317f -4 0) 1))
//@pbe (constraint (= (f317f -4 6) 13))
//@pbe (constraint (= (f317f 5 0) 1))