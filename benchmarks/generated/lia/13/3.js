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

function f935f(x_0, x_1, x_2)
{
	return subtract(add(x_0, x_1), mult(x_2, x_1));
}

function f996f(x_0, x_1, x_2)
{
	return mult(decrement(x_1), decrement(x_2));
}

function f799f(x_0)
{
	return add(subtract(x_0, x_0), decrement(x_0));
}

//@pbe (constraint (= (f520f -3 5) 0))
//@pbe (constraint (= (f520f -1 5) 0))
//@pbe (constraint (= (f520f 4 2) 0))