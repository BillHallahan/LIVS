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

function f811f(x_0, x_1)
{
	return subtract(subtract(x_1, x_0), x_1);
}

//@pbe (constraint (= (f804f -3) -0))
//@pbe (constraint (= (f804f -5) -0))
//@pbe (constraint (= (f804f 8) 0))
//@pbe (constraint (= (f804f 8) 0))