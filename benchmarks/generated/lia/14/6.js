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

function f370f(x_0, x_1, x_2)
{
	return increment(double(x_2));
}

function f449f(x_0, x_1, x_2)
{
	return mult(decrement(x_1), mult(x_2, x_2));
}

function f323f(x_0, x_1)
{
	return double(double(x_0));
}

function f978f(x_0, x_1)
{
	return double(f449f(x_0, x_0, x_0));
}

function f841f(x_0)
{
	return f449f(x_0, f370f(x_0, x_0, x_0), f978f(x_0, x_0));
}

function f261f(x_0, x_1, x_2)
{
	return add(x_2, increment(x_0));
}

//@pbe (constraint (= (f745f -4) -21744110796800000))
//@pbe (constraint (= (f745f 5) 101378560000000000))
//@pbe (constraint (= (f745f -2) -39813120000))