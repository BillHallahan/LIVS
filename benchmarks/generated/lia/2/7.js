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

function f1f(x_0)
{
	return subtract(increment(x_0), add(x_0, x_0));
}

function f100f(x_0)
{
	return f1f(increment(x_0));
}

function f206f(x_0)
{
	return increment(decrement(x_0));
}

function f668f(x_0)
{
	return add(double(x_0), subtract(x_0, x_0));
}

function f923f(x_0)
{
	return subtract(mult(x_0, x_0), f668f(x_0));
}

function f395f(x_0, x_1)
{
	return f1f(f100f(x_0));
}

function f86f(x_0)
{
	return f668f(f1f(x_0));
}

//@pbe (constraint (= (f361f 1 6 1) 0))
//@pbe (constraint (= (f361f 6 2 -5) 99))
//@pbe (constraint (= (f361f 0 2 -5) 15))
//@pbe (constraint (= (f361f 2 10 0) 0))
//@pbe (constraint (= (f361f 0 4 -3) 3))