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

function f726f(x_0)
{
	return increment(f869f(x_0, x_0));
}

//@pbe (constraint (= (f460f 4 3 8) 36))
//@pbe (constraint (= (f460f 0 1 0) 4))
//@pbe (constraint (= (f460f 1 2 3) 16))
//@pbe (constraint (= (f460f 0 6 4) 144))