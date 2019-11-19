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

function f0f(x_0, x_1)
{
	return mult(add(x_1, x_0), mult(x_1, x_0));
}

function f28f(x_0, x_1)
{
	return increment(f0f(x_1, x_1));
}

function f915f(x_0, x_1)
{
	return increment(f28f(x_0, x_0));
}

//@pbe (constraint (= (f862f 2 1) 0))
//@pbe (constraint (= (f862f -3 0) -12))
//@pbe (constraint (= (f862f 4 9) 384))
//@pbe (constraint (= (f862f -1 -5) -42))
//@pbe (constraint (= (f862f -4 8) -84))