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

function f263f(x_0, x_1, x_2)
{
	return add(f88f(x_1), x_1);
}

//@pbe (constraint (= (f215f 4) 32))
//@pbe (constraint (= (f215f 8) 128))
//@pbe (constraint (= (f215f -1) 2))