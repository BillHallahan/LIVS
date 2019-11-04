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

//@pbe (constraint (= (f78 "hello, world!" 2 "") 16))
//@pbe (constraint (= (f78 "hello" 4 "hello") 128))
//@pbe (constraint (= (f78 "asdf" 6 "hi") 432))
//@pbe (constraint (= (f78 "hello, world!" 6 "asdf") 432))
//@pbe (constraint (= (f78 "" 10 "asdf") 2000))