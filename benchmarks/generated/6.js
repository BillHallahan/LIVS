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

function f10(x_0, x_1, x_2)
{
	return mult(subtract(x_0, x_0), f0(x_0, x_2, x_2));
}

function f80(x_0, x_1)
{
	return f0(f10(x_0, x_0, x_1), f3(x_1, x_0, x_1), concat(x_1, x_1));
}

//@pbe (constraint (= (f65 5 "hi") 2000))
//@pbe (constraint (= (f65 2 "hello") 128))
//@pbe (constraint (= (f65 4 "hello, world!") 1024))