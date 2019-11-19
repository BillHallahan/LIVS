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

//@pbe (constraint (= (f652f 1 7) -1))
//@pbe (constraint (= (f652f 8 7) -64))
//@pbe (constraint (= (f652f 8 -1) -64))
//@pbe (constraint (= (f652f 8 4) -64))
//@pbe (constraint (= (f652f -2 -3) -4))