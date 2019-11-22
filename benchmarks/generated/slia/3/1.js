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

function f397f(x_0, x_1)
{
	return concat(beforeAfter(x_1), x_1);
}

//@pbe (constraint (= (f43f 6) "12"))
//@pbe (constraint (= (f43f 7) "14"))
//@pbe (constraint (= (f43f 7) "14"))