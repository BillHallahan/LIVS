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

function f257f(x_0, x_1)
{
	return toStr(mult(x_0, x_0));
}

function f833f(x_0, x_1, x_2)
{
	return len(toStr(x_2));
}

function f307f(x_0)
{
	return beforeAfter(toStr(x_0));
}

//@pbe (constraint (= (f587f "mno pqr st" 9 "mno pqr st") "81"))
//@pbe (constraint (= (f587f "vvvvv" 6 "hello world") "36"))
//@pbe (constraint (= (f587f "asdf" 8 "hello world") "64"))