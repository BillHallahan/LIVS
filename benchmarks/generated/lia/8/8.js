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

function f131f(x_0, x_1, x_2)
{
	return add(add(x_0, x_0), mult(x_1, x_0));
}

function f736f(x_0)
{
	return add(mult(x_0, x_0), f131f(x_0, x_0, x_0));
}

function f962f(x_0, x_1)
{
	return subtract(subtract(x_0, x_0), double(x_0));
}

function f148f(x_0)
{
	return mult(f962f(x_0, x_0), f736f(x_0));
}

function f908f(x_0, x_1, x_2)
{
	return subtract(x_2, f736f(x_1));
}

function f747f(x_0, x_1, x_2)
{
	return subtract(x_1, mult(x_2, x_2));
}

function f346f(x_0)
{
	return f908f(f736f(x_0), f962f(x_0, x_0), subtract(x_0, x_0));
}

function f853f(x_0)
{
	return f131f(double(x_0), mult(x_0, x_0), double(x_0));
}

//@pbe (constraint (= (f175f -3 7 -4) 2520))
//@pbe (constraint (= (f175f -4 -2 -2) 0))
//@pbe (constraint (= (f175f 10 -2 8) 0))
//@pbe (constraint (= (f175f 2 -2 -3) 0))