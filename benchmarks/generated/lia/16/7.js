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

function f237f(x_0, x_1, x_2)
{
	return subtract(f531f(x_1), subtract(x_1, x_2));
}

function f930f(x_0)
{
	return f237f(f955f(x_0, x_0), mult(x_0, x_0), add(x_0, x_0));
}

function f27f(x_0, x_1, x_2)
{
	return f531f(f930f(x_2));
}

//@pbe (constraint (= (f635f 5 5) 15))
//@pbe (constraint (= (f635f 3 4) 3))
//@pbe (constraint (= (f635f 1 0) -1))
//@pbe (constraint (= (f635f 9 1) 63))