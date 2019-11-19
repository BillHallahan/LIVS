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

function f480f(x_0, x_1, x_2)
{
	return increment(decrement(x_1));
}

//@pbe (constraint (= (f368f -1 6 -4) 2))
//@pbe (constraint (= (f368f 3 5 7) -2))
//@pbe (constraint (= (f368f 3 6 2) -2))
//@pbe (constraint (= (f368f 8 4 -4) -7))