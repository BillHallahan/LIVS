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

function f175f(x_0, x_1, x_2)
{
	return f736f(f131f(x_2, x_1, x_1));
}

//@pbe (constraint (= (f626f 6 3) -395))
//@pbe (constraint (= (f626f 9 8) -1360))
//@pbe (constraint (= (f626f 10 2) -1944))
//@pbe (constraint (= (f626f -1 1) -6))