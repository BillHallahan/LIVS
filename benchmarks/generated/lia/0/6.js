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

function f0f(x_0, x_1)
{
	return mult(add(x_1, x_0), mult(x_1, x_0));
}

function f28f(x_0, x_1)
{
	return increment(f0f(x_1, x_1));
}

function f915f(x_0, x_1)
{
	return increment(f28f(x_0, x_0));
}

function f862f(x_0, x_1)
{
	return f0f(decrement(x_1), x_0);
}

function f994f(x_0)
{
	return increment(decrement(x_0));
}

function f850f(x_0, x_1)
{
	return decrement(f0f(x_0, x_0));
}

//@pbe (constraint (= (f61f 5) 31251))
//@pbe (constraint (= (f61f 0) 1))
//@pbe (constraint (= (f61f 5) 31251))
//@pbe (constraint (= (f61f 1) 3))
//@pbe (constraint (= (f61f 4) 8193))