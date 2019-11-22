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

function f530f(x_0, x_1)
{
	return add(f833f(x_0, x_1, x_0), mult(x_0, x_0));
}

//@pbe (constraint (= (f928f "asdf" 4 "mno pqr st") "mno pqr stmno pqr stmno pqr st"))
//@pbe (constraint (= (f928f "asdf" 6 "xyz") "xyzxyzxyz"))
//@pbe (constraint (= (f928f "hello world" 1 "ab cd") "ab cdab cdab cd"))