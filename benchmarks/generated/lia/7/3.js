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

//@pbe (constraint (= (f36f 0 6 6) 50))
//@pbe (constraint (= (f36f 1 1 6) 40))
//@pbe (constraint (= (f36f 2 1 1) 5))