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

function f368f(x_0, x_1, x_2)
{
	return subtract(increment(x_0), double(x_0));
}

function f550f(x_0, x_1)
{
	return decrement(f368f(x_0, x_1, x_0));
}

function f985f(x_0)
{
	return f550f(increment(x_0), add(x_0, x_0));
}

function f773f(x_0, x_1)
{
	return subtract(subtract(x_1, x_1), double(x_0));
}

function f69f(x_0, x_1)
{
	return increment(f368f(x_0, x_1, x_0));
}

//@pbe (constraint (= (f896f -1) -1))
//@pbe (constraint (= (f896f 1) 3))