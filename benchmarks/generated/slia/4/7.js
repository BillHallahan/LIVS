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
	return (x_0 + 10) + "";
}

function beforeAfter(x_0)
{
	return 'B' + x_0 + 'A';
}

function f365f(x_0, x_1, x_2)
{
	return beforeAfter(concat(x_0, x_0));
}

function f337f(x_0, x_1)
{
	return beforeAfter(f365f(x_1, x_0, x_0));
}

function f450f(x_0)
{
	return len(toStr(x_0));
}

function f969f(x_0, x_1)
{
	return f450f(x_0);
}

function f766f(x_0, x_1, x_2)
{
	return f337f(x_0, f337f(x_0, x_2));
}

function f309f(x_0, x_1, x_2)
{
	return toStr(add(x_0, x_0));
}

function f296f(x_0)
{
	return f337f(len(x_0), x_0);
}

//@pbe (constraint (= (f142f 8 "mno pqr st") "BBmno pqr stmno pqr stAA"))
//@pbe (constraint (= (f142f 9 "asdf") "BBasdfasdfAA"))
//@pbe (constraint (= (f142f -1 "asdf") "BBasdfasdfAA"))
//@pbe (constraint (= (f142f 8 "mno pqr st") "BBmno pqr stmno pqr stAA"))