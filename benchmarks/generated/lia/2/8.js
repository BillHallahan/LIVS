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

function f361f(x_0, x_1, x_2)
{
	return f923f(subtract(x_0, x_2));
}

//@pbe (constraint (= (f481f 1) 3))
//@pbe (constraint (= (f481f -3) -5))