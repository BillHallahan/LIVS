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
	return x_0 - x_0;
}

function f0f(x_0, x_1, x_2)
{
	return mult(add(x_0, x_1), x_1);
}

//@pbe (constraint (= (f46f 8 9 5) 15))
//@pbe (constraint (= (f46f 3 0 7) 8))
//@pbe (constraint (= (f46f -3 5 7) 13))
//@pbe (constraint (= (f46f 4 -1 10) 10))