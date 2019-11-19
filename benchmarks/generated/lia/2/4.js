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

//@pbe (constraint (= (f923f 9) 63))
//@pbe (constraint (= (f923f 4) 8))
//@pbe (constraint (= (f923f 4) 8))
//@pbe (constraint (= (f923f 7) 35))
//@pbe (constraint (= (f923f 5) 15))