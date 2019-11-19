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

//@pbe (constraint (= (f681f -2) 2))
//@pbe (constraint (= (f681f -1) 0))
//@pbe (constraint (= (f681f 5) 72))
//@pbe (constraint (= (f681f 10) 242))