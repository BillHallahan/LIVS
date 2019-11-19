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

function f53f(x_0, x_1)
{
	return double(x_0);
}

function f355f(x_0)
{
	return add(x_0, subtract(x_0, x_0));
}

function f112f(x_0, x_1, x_2)
{
	return subtract(add(x_2, x_2), x_2);
}

function f271f(x_0, x_1)
{
	return subtract(add(x_0, x_0), f355f(x_1));
}

function f406f(x_0, x_1)
{
	return decrement(x_0);
}

function f456f(x_0, x_1)
{
	return increment(x_0);
}

function f649f(x_0)
{
	return increment(f456f(x_0, x_0));
}

function f900f(x_0)
{
	return increment(f355f(x_0));
}

//@pbe (constraint (= (f837f 10) 18))
//@pbe (constraint (= (f837f 3) 4))
//@pbe (constraint (= (f837f 0) -2))
//@pbe (constraint (= (f837f -2) -6))
//@pbe (constraint (= (f837f 4) 6))