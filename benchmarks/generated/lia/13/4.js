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

function f520f(x_0, x_1)
{
	return mult(subtract(x_0, x_0), add(x_1, x_1));
}

//@pbe (constraint (= (f276f 10 -4 3) 2))
//@pbe (constraint (= (f276f 1 -1 6) -4))
//@pbe (constraint (= (f276f 1 6 1) -6))
//@pbe (constraint (= (f276f -3 6 -5) -0))