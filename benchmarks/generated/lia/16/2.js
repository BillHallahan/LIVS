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

//@pbe (constraint (= (f531f 5) 11))
//@pbe (constraint (= (f531f 8) 17))