function add(x_0, x_1)
{
	return x_0 + x_1;
}

function mult(x_0, x_1)
{
	return x_0 * x_1;
}

function concat(x_0, x_1)
{
	return x_0 + x_1;
}

function len(x_0)
{
	return x_0.length;
}

function toStr(x_0)
{
	return x_0 + "";
}

function beforeAfter(x_0)
{
	return 'B' + x_0 + 'A';
}

function f998f(x_0)
{
	return add(x_0, mult(x_0, x_0));
}

function f351f(x_0, x_1, x_2)
{
	return beforeAfter(concat(x_0, x_0));
}

//@pbe (constraint (= (f532f 7 "asdf") 3192))
//@pbe (constraint (= (f532f 3 "hello world") 156))
//@pbe (constraint (= (f532f 4 "mno pqr st") 420))
//@pbe (constraint (= (f532f 4 "ab cd") 420))