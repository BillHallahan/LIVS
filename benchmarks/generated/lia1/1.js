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

//@pbe (constraint (= (f61f -4) -2))
//@pbe (constraint (= (f61f 5) 7))
//@pbe (constraint (= (f61f 4) 6))
//@pbe (constraint (= (f61f 7) 9))
//@pbe (constraint (= (f61f 6) 8))