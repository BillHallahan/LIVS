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

function f46f(x_0, x_1, x_2)
{
	return increment(add(x_1, x_2));
}

function f98f(x_0, x_1)
{
	return f0f(add(x_1, x_1), f0f(x_0, x_0, x_1), mult(x_1, x_0));
}

function f83f(x_0, x_1)
{
	return f46f(add(x_1, x_1), f98f(x_1, x_1), increment(x_0));
}

function f43f(x_0, x_1)
{
	return increment(x_1);
}

function f69f(x_0)
{
	return f43f(x_0, increment(x_0));
}

//@pbe (constraint (= (f90f -2 7 8) 112))
//@pbe (constraint (= (f90f 0 -4 1) 4))
//@pbe (constraint (= (f90f 6 1 1) 16))
//@pbe (constraint (= (f90f 10 -1 -4) -56))