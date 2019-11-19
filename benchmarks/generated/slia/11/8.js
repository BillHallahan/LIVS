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

function f369f(x_0, x_1, x_2)
{
	return add(mult(x_0, x_2), x_2);
}

function f222f(x_0, x_1)
{
	return add(mult(x_1, x_1), add(x_1, x_1));
}

function f135f(x_0, x_1, x_2)
{
	return mult(f369f(x_0, x_2, x_0), add(x_0, x_0));
}

function f983f(x_0, x_1)
{
	return add(add(x_0, x_0), x_0);
}

function f134f(x_0, x_1, x_2)
{
	return concat(beforeAfter(x_1), toStr(x_2));
}

function f705f(x_0, x_1, x_2)
{
	return f134f(len(x_1), toStr(x_2), x_2);
}

function f360f(x_0, x_1, x_2)
{
	return f983f(f983f(x_0, x_2), toStr(x_0));
}

function f144f(x_0, x_1)
{
	return add(mult(x_1, x_1), f222f(x_0, x_1));
}

//@pbe (constraint (= (f3f 6 "vvvvv" 9) "B94A94"))
//@pbe (constraint (= (f3f 0 "ab cd" 4) "B10A10"))