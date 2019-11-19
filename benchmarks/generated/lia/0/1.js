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

function f0f(x_0, x_1)
{
	return mult(add(x_1, x_0), mult(x_1, x_0));
}

//@pbe (constraint (= (f28f -2 -4) -127))
//@pbe (constraint (= (f28f 5 9) 1459))
//@pbe (constraint (= (f28f -4 6) 433))
//@pbe (constraint (= (f28f 7 -5) -249))
//@pbe (constraint (= (f28f -3 8) 1025))