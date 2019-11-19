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

function f423f(x_0, x_1, x_2)
{
	return add(increment(x_1), mult(x_1, x_0));
}

//@pbe (constraint (= (f774f -3 4) 7))
//@pbe (constraint (= (f774f 1 -2) -5))
//@pbe (constraint (= (f774f -4 5) 9))
//@pbe (constraint (= (f774f 2 7) 13))