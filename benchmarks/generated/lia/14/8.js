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

function f745f(x_0)
{
	return f841f(f978f(x_0, x_0));
}

function f6f(x_0)
{
	return f745f(add(x_0, x_0));
}

//@pbe (constraint (= (f379f 10 -5) -899700))
//@pbe (constraint (= (f379f 7 6) 1554840))
//@pbe (constraint (= (f379f 3 5) 399800))
//@pbe (constraint (= (f379f -2 2) 248))
//@pbe (constraint (= (f379f 6 6) 1554840))