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

function f774f(x_0, x_1)
{
	return decrement(add(x_1, x_1));
}

//@pbe (constraint (= (f77f 6 9 1) 55))
//@pbe (constraint (= (f77f 0 0 -1) 1))
//@pbe (constraint (= (f77f -2 8 6) 15))
//@pbe (constraint (= (f77f 2 3 -3) 3))
//@pbe (constraint (= (f77f 8 10 5) 105))