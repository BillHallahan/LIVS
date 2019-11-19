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

function f935f(x_0, x_1, x_2)
{
	return subtract(add(x_0, x_1), mult(x_2, x_1));
}

//@pbe (constraint (= (f996f -1 8 1) 0))
//@pbe (constraint (= (f996f 8 5 5) 16))
//@pbe (constraint (= (f996f -1 2 -5) -6))
//@pbe (constraint (= (f996f -4 -3 8) -28))