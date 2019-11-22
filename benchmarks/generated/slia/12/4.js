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

function f272f(x_0, x_1, x_2)
{
	return add(x_0, add(x_0, x_0));
}

function f58f(x_0, x_1)
{
	return beforeAfter(x_0);
}

function f604f(x_0, x_1, x_2)
{
	return add(add(x_1, x_2), mult(x_1, x_2));
}

function f757f(x_0, x_1)
{
	return toStr(x_0);
}

//@pbe (constraint (= (f474f 4 "404") "404404404"))
//@pbe (constraint (= (f474f 1 "mno pqr st") "mno pqr stmno pqr stmno pqr st"))
//@pbe (constraint (= (f474f 6 "ab cd") "ab cdab cdab cd"))