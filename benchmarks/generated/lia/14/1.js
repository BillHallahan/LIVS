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

//@pbe (constraint (= (f449f 8 1 0) 0))
//@pbe (constraint (= (f449f -5 9 -5) 200))
//@pbe (constraint (= (f449f 9 3 4) 32))
//@pbe (constraint (= (f449f 5 -3 1) -4))
//@pbe (constraint (= (f449f -3 6 0) 0))