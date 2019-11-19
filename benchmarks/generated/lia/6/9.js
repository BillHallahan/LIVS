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

function f713f(x_0, x_1, x_2)
{
	return add(x_1, x_2);
}

function f120f(x_0, x_1)
{
	return double(x_1);
}

function f367f(x_0, x_1, x_2)
{
	return f120f(increment(x_1), f713f(x_2, x_1, x_1));
}

function f614f(x_0, x_1, x_2)
{
	return f713f(x_1, decrement(x_0), increment(x_0));
}

function f279f(x_0, x_1, x_2)
{
	return f367f(x_1, f614f(x_1, x_1, x_0), f614f(x_2, x_0, x_2));
}

function f129f(x_0, x_1)
{
	return f367f(increment(x_1), x_0, increment(x_0));
}

function f55f(x_0)
{
	return mult(f713f(x_0, x_0, x_0), f713f(x_0, x_0, x_0));
}

function f247f(x_0)
{
	return f55f(f279f(x_0, x_0, x_0));
}

function f162f(x_0)
{
	return f120f(x_0, mult(x_0, x_0));
}

//@pbe (constraint (= (f249f 1) 4096))
//@pbe (constraint (= (f249f 4) 65536))
//@pbe (constraint (= (f249f 3) 36864))
//@pbe (constraint (= (f249f 6) 147456))
//@pbe (constraint (= (f249f -5) 102400))