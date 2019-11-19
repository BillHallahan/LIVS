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

function f916f(x_0)
{
	return decrement(mult(x_0, x_0));
}

//@pbe (constraint (= (f105f -1 0) -2))
//@pbe (constraint (= (f105f -2 8) 62))
//@pbe (constraint (= (f105f 5 9) 79))
//@pbe (constraint (= (f105f 0 9) 79))
//@pbe (constraint (= (f105f 9 1) -1))