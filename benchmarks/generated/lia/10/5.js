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

function f869f(x_0, x_1)
{
	return mult(double(x_1), add(x_1, x_1));
}

function f726f(x_0)
{
	return increment(f869f(x_0, x_0));
}

function f460f(x_0, x_1, x_2)
{
	return decrement(f726f(x_1));
}

function f341f(x_0, x_1, x_2)
{
	return subtract(subtract(x_1, x_0), mult(x_0, x_2));
}

function f891f(x_0, x_1, x_2)
{
	return decrement(f460f(x_2, x_1, x_1));
}

//@pbe (constraint (= (f809f -4 4) 0))
//@pbe (constraint (= (f809f 4 7) 154))
//@pbe (constraint (= (f809f -5 7) 28))