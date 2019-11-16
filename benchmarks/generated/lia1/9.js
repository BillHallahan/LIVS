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
	return x_0 - x_0;
}

function f0f(x_0)
{
	return increment(increment(x_0));
}

function f61f(x_0)
{
	return increment(increment(x_0));
}

function f45f(x_0, x_1, x_2)
{
	return f61f(x_1);
}

function f91f(x_0, x_1, x_2)
{
	return mult(add(x_1, x_1), mult(x_2, x_2));
}

function f66f(x_0)
{
	return subtract(increment(x_0), mult(x_0, x_0));
}

function f81f(x_0)
{
	return subtract(mult(x_0, x_0), f45f(x_0, x_0, x_0));
}

function f9f(x_0, x_1, x_2)
{
	return f66f(x_1);
}

function f96f(x_0, x_1)
{
	return mult(add(x_0, x_1), x_0);
}

function f98f(x_0, x_1)
{
	return subtract(f45f(x_1, x_0, x_0), x_1);
}

//@pbe (constraint (= (f84f 8 5) 1026))
//@pbe (constraint (= (f84f 0 2) 2))
//@pbe (constraint (= (f84f -4 9) -126))
//@pbe (constraint (= (f84f 9 4) 1460))
//@pbe (constraint (= (f84f 8 6) 1026))