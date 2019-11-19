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

function f667f(x_0, x_1, x_2)
{
	return increment(subtract(x_2, x_1));
}

function f287f(x_0)
{
	return add(add(x_0, x_0), increment(x_0));
}

function f37f(x_0, x_1)
{
	return decrement(increment(x_1));
}

function f298f(x_0, x_1)
{
	return subtract(increment(x_1), f287f(x_1));
}

function f558f(x_0, x_1)
{
	return f667f(f287f(x_0), f667f(x_0, x_1, x_0), x_1);
}

function f823f(x_0)
{
	return increment(f298f(x_0, x_0));
}

//@pbe (constraint (= (f106f -5) -9))
//@pbe (constraint (= (f106f 8) 17))
//@pbe (constraint (= (f106f 7) 15))
//@pbe (constraint (= (f106f 10) 21))
//@pbe (constraint (= (f106f 6) 13))