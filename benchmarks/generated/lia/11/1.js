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

//@pbe (constraint (= (f287f 2) 7))
//@pbe (constraint (= (f287f -4) -11))
//@pbe (constraint (= (f287f 3) 10))
//@pbe (constraint (= (f287f 10) 31))
//@pbe (constraint (= (f287f 3) 10))