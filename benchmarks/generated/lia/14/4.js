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

//@pbe (constraint (= (f841f 3) 7776))
//@pbe (constraint (= (f841f 7) 4840416))
//@pbe (constraint (= (f841f -1) -32))