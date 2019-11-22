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

//@pbe (constraint (= (f563f "xyz" 10 6) "xyzxyz3"))
//@pbe (constraint (= (f563f "asdf" 3 10) "asdfasdf4"))
//@pbe (constraint (= (f563f "mno pqr st" 5 10) "mno pqr stmno pqr st10"))
//@pbe (constraint (= (f563f "xyz" 6 4) "xyzxyz3"))