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
	return x_0 - x_0;
}

function f0f(x_0)
{
	return increment(increment(x_0));
}

function f61f(x_0)
{
	return increment(increment(x_0));
}

function f45f(x_0, x_1, x_2)
{
	return f61f(x_1);
}

function f91f(x_0, x_1, x_2)
{
	return mult(add(x_1, x_1), mult(x_2, x_2));
}

//@pbe (constraint (= (f66f 2) 0))
//@pbe (constraint (= (f66f -3) 0))