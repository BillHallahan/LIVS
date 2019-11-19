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

function f366f(x_0, x_1, x_2)
{
	return mult(x_0, subtract(x_1, x_1));
}

function f650f(x_0, x_1, x_2)
{
	return f366f(decrement(x_2), decrement(x_1), double(x_1));
}

function f652f(x_0, x_1)
{
	return subtract(f366f(x_1, x_1, x_1), mult(x_0, x_0));
}

function f184f(x_0)
{
	return add(f650f(x_0, x_0, x_0), add(x_0, x_0));
}

function f982f(x_0, x_1, x_2)
{
	return mult(f652f(x_1, x_1), increment(x_0));
}

function f588f(x_0, x_1)
{
	return double(x_0);
}

//@pbe (constraint (= (f81f -4 -2 -5) -64))
//@pbe (constraint (= (f81f 7 5 -5) -196))