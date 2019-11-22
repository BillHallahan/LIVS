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

function f810f(x_0)
{
	return concat(concat(x_0, x_0), x_0);
}

//@pbe (constraint (= (f257f 10 "ab cd") "100"))
//@pbe (constraint (= (f257f 9 "vvvvv") "81"))
//@pbe (constraint (= (f257f 7 "asdf") "49"))
//@pbe (constraint (= (f257f 2 "xyz") "4"))