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

function f85f(x_0, x_1, x_2)
{
	return mult(decrement(x_2), add(x_0, x_1));
}

function f727f(x_0, x_1)
{
	return increment(x_1);
}

function f625f(x_0, x_1, x_2)
{
	return double(f727f(x_2, x_2));
}

function f317f(x_0, x_1)
{
	return increment(add(x_1, x_1));
}

//@pbe (constraint (= (f513f -3) -184))
//@pbe (constraint (= (f513f 2) 21))
//@pbe (constraint (= (f513f -1) -6))
//@pbe (constraint (= (f513f 5) 624))
//@pbe (constraint (= (f513f 5) 624))