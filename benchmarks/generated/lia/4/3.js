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

function f890f(x_0, x_1)
{
	return subtract(add(x_0, x_0), mult(x_1, x_0));
}

function f387f(x_0)
{
	return increment(decrement(x_0));
}

function f461f(x_0)
{
	return f387f(increment(x_0));
}

//@pbe (constraint (= (f555f 9) -63))
//@pbe (constraint (= (f555f -2) -8))
//@pbe (constraint (= (f555f -5) -35))
//@pbe (constraint (= (f555f 7) -35))
//@pbe (constraint (= (f555f -2) -8))