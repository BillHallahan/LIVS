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

function f47(x_0)
{
	return subtract(subtract(x_0, x_0), subtract(x_0, x_0));
}

function f3(x_0, x_1, x_2)
{
	return concat(concat(x_0, x_2), x_0);
}

function f78(x_0, x_1, x_2)
{
	return mult(add(x_1, x_1), mult(x_1, x_1));
}

//@pbe (constraint (= (f10 0 -2 "asdf") 0))
//@pbe (constraint (= (f10 2 1 "hello") 0))