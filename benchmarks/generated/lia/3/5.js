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

function f77f(x_0, x_1, x_2)
{
	return mult(f774f(x_2, x_0), decrement(x_0));
}

function f88f(x_0)
{
	return subtract(f774f(x_0, x_0), x_0);
}

function f630f(x_0, x_1, x_2)
{
	return decrement(add(x_1, x_2));
}

//@pbe (constraint (= (f263f 1 9 -5) 17))
//@pbe (constraint (= (f263f 6 -4 3) -9))
//@pbe (constraint (= (f263f 3 3 -5) 5))
//@pbe (constraint (= (f263f 5 9 5) 17))
//@pbe (constraint (= (f263f 4 6 7) 11))