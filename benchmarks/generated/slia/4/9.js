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

function f135f(x_0, x_1, x_2)
{
	return len(x_0);
}

function f569f(x_0)
{
	return toStr(f135f(x_0, x_0, x_0));
}

function f455f(x_0, x_1, x_2)
{
	return f569f(x_0);
}

function f560f(x_0, x_1, x_2)
{
	return add(x_2, x_2);
}

function f66f(x_0, x_1, x_2)
{
	return f569f(concat(x_2, x_2));
}

function f970f(x_0, x_1, x_2)
{
	return f560f(mult(x_2, x_2), f135f(x_0, x_1, x_1), x_2);
}

function f511f(x_0, x_1)
{
	return concat(f569f(x_0), x_1);
}

function f563f(x_0, x_1, x_2)
{
	return concat(concat(x_0, x_0), f569f(x_0));
}

function f460f(x_0, x_1, x_2)
{
	return add(len(x_0), add(x_1, x_2));
}

//@pbe (constraint (= (f236f 7 "mno pqr st") "24"))
//@pbe (constraint (= (f236f 7 "asdf") "12"))
//@pbe (constraint (= (f236f 3 "asdf") "12"))
//@pbe (constraint (= (f236f 7 "ab cd") "14"))