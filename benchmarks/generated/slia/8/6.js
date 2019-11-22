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

function f36f(x_0)
{
	return toStr(x_0);
}

function f759f(x_0, x_1, x_2)
{
	return f36f(mult(x_1, x_1));
}

function f916f(x_0)
{
	return f36f(x_0);
}

function f72f(x_0, x_1, x_2)
{
	return toStr(len(x_0));
}

function f258f(x_0, x_1, x_2)
{
	return f36f(add(x_2, x_2));
}

function f495f(x_0, x_1, x_2)
{
	return f258f(beforeAfter(x_2), x_1, x_1);
}

//@pbe (constraint (= (f328f 8 "mno pqr st") "10mno pqr stmno pqr st"))
//@pbe (constraint (= (f328f 7 "hello world") "11hello worldhello world"))