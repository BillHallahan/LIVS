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

function f90f(x_0, x_1, x_2)
{
	return mult(add(x_2, x_2), f46f(x_0, x_2, x_0));
}

//@pbe (constraint (= (f22f -3) 29))
//@pbe (constraint (= (f22f 10) 419))
//@pbe (constraint (= (f22f 10) 419))
//@pbe (constraint (= (f22f -2) 11))
//@pbe (constraint (= (f22f -4) 55))