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

function f713f(x_0, x_1, x_2)
{
	return add(x_1, x_2);
}

function f120f(x_0, x_1)
{
	return double(x_1);
}

//@pbe (constraint (= (f367f 3 8 2) 32))
//@pbe (constraint (= (f367f -3 -3 9) -12))
//@pbe (constraint (= (f367f 5 0 7) 0))
//@pbe (constraint (= (f367f -3 4 5) 16))
//@pbe (constraint (= (f367f 1 -5 0) -20))