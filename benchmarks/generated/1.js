function add(x_0, x_1)
{
	return x_0 + x_1;
}

function subtract(x_0, x_1)
{
	return x_0 - x_1;
}

function mult(x_0, x_1)
{
	return x_0 * x_1;
}

function concat(x_0, x_1)
{
	return x_0 + x_1;
}

function f0(x_0, x_1, x_2)
{
	return mult(add(x_0, x_0), mult(x_0, x_0));
}

//@pbe (constraint (= (f47 8) 0))
//@pbe (constraint (= (f47 6) 0))
//@pbe (constraint (= (f47 2) 0))
//@pbe (constraint (= (f47 1) 0))
//@pbe (constraint (= (f47 8) 0))