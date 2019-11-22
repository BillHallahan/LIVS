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

function f587f(x_0, x_1, x_2)
{
	return f257f(x_1, f810f(x_0));
}

//@pbe (constraint (= (f530f 8 "mno pqr st") 65))
//@pbe (constraint (= (f530f 1 "ab cd") 2))
//@pbe (constraint (= (f530f 8 "ab cd") 65))
//@pbe (constraint (= (f530f 6 "asdf") 37))