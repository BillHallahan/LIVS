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

function f522f(x_0, x_1)
{
	return increment(subtract(x_1, x_0));
}

function f36f(x_0, x_1, x_2)
{
	return f111f(mult(x_2, x_2), increment(x_1), increment(x_1));
}

function f827f(x_0, x_1, x_2)
{
	return mult(increment(x_0), x_2);
}

function f681f(x_0)
{
	return f111f(f827f(x_0, x_0, x_0), f36f(x_0, x_0, x_0), x_0);
}

function f313f(x_0)
{
	return increment(f111f(x_0, x_0, x_0));
}

function f356f(x_0)
{
	return f681f(x_0);
}

function f529f(x_0, x_1, x_2)
{
	return f313f(x_0);
}

//@pbe (constraint (= (f769f -4) 55))
//@pbe (constraint (= (f769f 2) 55))