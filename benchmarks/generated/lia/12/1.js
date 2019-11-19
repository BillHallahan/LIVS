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

function f687f(x_0, x_1)
{
	return subtract(increment(x_1), increment(x_0));
}

//@pbe (constraint (= (f270f -1) 2))
//@pbe (constraint (= (f270f 2) -1))
//@pbe (constraint (= (f270f 8) -7))
//@pbe (constraint (= (f270f 3) -2))
//@pbe (constraint (= (f270f 7) -6))