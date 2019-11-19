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

function f667f(x_0, x_1, x_2)
{
	return increment(subtract(x_2, x_1));
}

function f287f(x_0)
{
	return add(add(x_0, x_0), increment(x_0));
}

function f37f(x_0, x_1)
{
	return decrement(increment(x_1));
}

function f298f(x_0, x_1)
{
	return subtract(increment(x_1), f287f(x_1));
}

//@pbe (constraint (= (f558f -4 10) 24))
//@pbe (constraint (= (f558f -1 10) 21))
//@pbe (constraint (= (f558f 1 2) 3))
//@pbe (constraint (= (f558f -3 -4) -5))