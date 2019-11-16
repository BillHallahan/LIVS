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

//@pbe (constraint (= (f91f 1 10 -3) 180))
//@pbe (constraint (= (f91f -1 -5 0) -0))
//@pbe (constraint (= (f91f 6 -2 6) -144))
//@pbe (constraint (= (f91f -3 0 -2) 0))