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

function f394f(x_0, x_1)
{
	return mult(mult(x_1, x_0), x_0);
}

function f525f(x_0, x_1, x_2)
{
	return double(f849f(x_0));
}

//@pbe (constraint (= (f499f 1) 0))
//@pbe (constraint (= (f499f -1) 2))
//@pbe (constraint (= (f499f -5) 150))