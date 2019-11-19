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

function f713f(x_0, x_1, x_2)
{
	return add(x_1, x_2);
}

function f120f(x_0, x_1)
{
	return double(x_1);
}

function f367f(x_0, x_1, x_2)
{
	return f120f(increment(x_1), f713f(x_2, x_1, x_1));
}

//@pbe (constraint (= (f614f -1 9 7) -2))
//@pbe (constraint (= (f614f 1 5 0) 2))
//@pbe (constraint (= (f614f 10 9 -3) 20))
//@pbe (constraint (= (f614f -2 -1 2) -4))