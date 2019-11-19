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

function f811f(x_0, x_1)
{
	return subtract(subtract(x_1, x_0), x_1);
}

function f804f(x_0)
{
	return mult(add(x_0, x_0), subtract(x_0, x_0));
}

function f92f(x_0, x_1, x_2)
{
	return add(x_0, add(x_2, x_0));
}

function f677f(x_0, x_1)
{
	return subtract(f804f(x_0), double(x_0));
}

function f786f(x_0, x_1, x_2)
{
	return decrement(f92f(x_1, x_0, x_1));
}

function f231f(x_0)
{
	return mult(f677f(x_0, x_0), f677f(x_0, x_0));
}

//@pbe (constraint (= (f172f 10) -200))
//@pbe (constraint (= (f172f -2) -8))
//@pbe (constraint (= (f172f 0) 0))
//@pbe (constraint (= (f172f 7) -98))
//@pbe (constraint (= (f172f -3) -18))