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

function f276f(x_0, x_1, x_2)
{
	return f996f(f996f(x_0, x_1, x_1), add(x_1, x_2), f520f(x_2, x_1));
}

function f920f(x_0)
{
	return f276f(x_0, decrement(x_0), f276f(x_0, x_0, x_0));
}

function f486f(x_0, x_1)
{
	return f799f(x_1);
}

//@pbe (constraint (= (f763f 6 5 6) 30))
//@pbe (constraint (= (f763f 0 2 4) 0))
//@pbe (constraint (= (f763f 8 7 -3) 70))
//@pbe (constraint (= (f763f -1 -5 7) 49))