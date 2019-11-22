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

function f950f(x_0, x_1, x_2)
{
	return beforeAfter(x_1);
}

function f75f(x_0, x_1, x_2)
{
	return add(add(x_1, x_1), add(x_0, x_0));
}

function f314f(x_0, x_1)
{
	return toStr(len(x_0));
}

function f844f(x_0, x_1, x_2)
{
	return f75f(x_2, add(x_2, x_2), f314f(x_0, x_1));
}

function f117f(x_0, x_1)
{
	return concat(beforeAfter(x_0), beforeAfter(x_0));
}

function f333f(x_0, x_1)
{
	return mult(add(x_1, x_1), f75f(x_1, x_1, x_0));
}

function f795f(x_0, x_1)
{
	return beforeAfter(toStr(x_1));
}

function f547f(x_0)
{
	return beforeAfter(toStr(x_0));
}

//@pbe (constraint (= (f556f 3 6 6) "B6AB6A"))
//@pbe (constraint (= (f556f 9 4 7) "B7AB7A"))