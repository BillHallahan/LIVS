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

function f172f(x_0)
{
	return f677f(mult(x_0, x_0), add(x_0, x_0));
}

function f104f(x_0)
{
	return f172f(f677f(x_0, x_0));
}

function f646f(x_0, x_1, x_2)
{
	return f811f(x_0, f786f(x_1, x_1, x_0));
}

//@pbe (constraint (= (f591f -4 3 7) -72))
//@pbe (constraint (= (f591f 0 2 0) -2))
//@pbe (constraint (= (f591f 7 -3 3) -8))
//@pbe (constraint (= (f591f 7 8 -2) -18))
//@pbe (constraint (= (f591f 10 10 7) -72))