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

//@pbe (constraint (= (f3 "hi" 8 "hello, world!") "hihello, world!hi"))
//@pbe (constraint (= (f3 "hello" 2 "hi") "hellohihello"))