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

//@pbe (constraint (= (f307f 10) "B10A"))
//@pbe (constraint (= (f307f 6) "B6A"))
//@pbe (constraint (= (f307f 1) "B1A"))