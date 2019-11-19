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

function f890f(x_0, x_1)
{
	return subtract(add(x_0, x_0), mult(x_1, x_0));
}

//@pbe (constraint (= (f387f -5) -5))
//@pbe (constraint (= (f387f 6) 6))
//@pbe (constraint (= (f387f 10) 10))
//@pbe (constraint (= (f387f -2) -2))
//@pbe (constraint (= (f387f -3) -3))