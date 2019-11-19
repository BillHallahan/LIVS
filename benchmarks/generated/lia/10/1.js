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

function f869f(x_0, x_1)
{
	return mult(double(x_1), add(x_1, x_1));
}

//@pbe (constraint (= (f726f 5) 101))
//@pbe (constraint (= (f726f 1) 5))
//@pbe (constraint (= (f726f 9) 325))
//@pbe (constraint (= (f726f -4) 65))
//@pbe (constraint (= (f726f -5) 101))