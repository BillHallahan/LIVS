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

function f85f(x_0, x_1, x_2)
{
	return mult(decrement(x_2), add(x_0, x_1));
}

function f727f(x_0, x_1)
{
	return increment(x_1);
}

function f625f(x_0, x_1, x_2)
{
	return double(f727f(x_2, x_2));
}

function f317f(x_0, x_1)
{
	return increment(add(x_1, x_1));
}

function f513f(x_0)
{
	return f85f(double(x_0), increment(x_0), f85f(x_0, x_0, x_0));
}

function f699f(x_0)
{
	return f513f(f513f(x_0));
}

function f122f(x_0)
{
	return f317f(x_0, add(x_0, x_0));
}

//@pbe (constraint (= (f950f 6 1 4) -6.408226530179906e+26))
//@pbe (constraint (= (f950f -3 5 10) 3.817364744064809e+85))