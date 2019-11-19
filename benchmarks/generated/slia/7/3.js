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

function f824f(x_0, x_1, x_2)
{
	return mult(x_2, x_2);
}

function f573f(x_0, x_1)
{
	return add(f824f(x_0, x_0, x_1), len(x_0));
}

function f191f(x_0, x_1, x_2)
{
	return f824f(concat(x_2, x_2), x_1, len(x_1));
}

//@pbe (constraint (= (f628f 1 1 "asdf") "12"))
//@pbe (constraint (= (f628f 9 3 "") "22"))