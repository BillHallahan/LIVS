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

function f916f(x_0)
{
	return decrement(mult(x_0, x_0));
}

function f105f(x_0, x_1)
{
	return decrement(f916f(x_1));
}

function f531f(x_0)
{
	return increment(add(x_0, x_0));
}

function f955f(x_0, x_1)
{
	return mult(double(x_0), x_1);
}

//@pbe (constraint (= (f237f 4 9 -3) 7))
//@pbe (constraint (= (f237f 9 6 -4) 3))
//@pbe (constraint (= (f237f 0 1 0) 2))