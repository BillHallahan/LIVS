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

function f849f(x_0)
{
	return mult(x_0, subtract(x_0, x_0));
}

function f394f(x_0, x_1)
{
	return mult(mult(x_1, x_0), x_0);
}

function f525f(x_0, x_1, x_2)
{
	return double(f849f(x_0));
}

function f499f(x_0)
{
	return subtract(mult(x_0, x_0), f394f(x_0, x_0));
}

function f216f(x_0, x_1)
{
	return subtract(add(x_1, x_0), decrement(x_1));
}

function f392f(x_0, x_1)
{
	return f499f(f394f(x_0, x_0));
}

function f548f(x_0, x_1, x_2)
{
	return f849f(mult(x_1, x_0));
}

function f307f(x_0, x_1, x_2)
{
	return decrement(decrement(x_2));
}

function f295f(x_0, x_1, x_2)
{
	return f394f(f548f(x_2, x_0, x_2), increment(x_2));
}

//@pbe (constraint (= (f921f 4) -258043))
//@pbe (constraint (= (f921f 10) -998999989))
//@pbe (constraint (= (f921f -3) 20410))
//@pbe (constraint (= (f921f 6) -10031033))
//@pbe (constraint (= (f921f 8) -133955575))