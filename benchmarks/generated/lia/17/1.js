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

function f849f(x_0)
{
	return mult(x_0, subtract(x_0, x_0));
}

//@pbe (constraint (= (f394f 0 0) 0))
//@pbe (constraint (= (f394f 5 4) 100))
//@pbe (constraint (= (f394f -3 8) 72))
//@pbe (constraint (= (f394f 2 1) 4))