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

function f804f(x_0)
{
	return mult(add(x_0, x_0), subtract(x_0, x_0));
}

//@pbe (constraint (= (f92f -2 -2 0) -4))
//@pbe (constraint (= (f92f 2 0 3) 7))
//@pbe (constraint (= (f92f 5 5 4) 14))
//@pbe (constraint (= (f92f -2 8 6) 2))