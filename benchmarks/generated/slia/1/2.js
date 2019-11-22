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

function f798f(x_0, x_1, x_2)
{
	return add(x_2, x_1);
}

function f514f(x_0)
{
	return toStr(mult(x_0, x_0));
}

//@pbe (constraint (= (f893f "vvvvv" 4 "404") "256"))
//@pbe (constraint (= (f893f "xyz" 10 "ab cd") "10000"))
//@pbe (constraint (= (f893f "ab cd" 1 "asdf") "1"))
//@pbe (constraint (= (f893f "xyz" 9 "ab cd") "6561"))