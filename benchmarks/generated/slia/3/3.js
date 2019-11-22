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

function f43f(x_0)
{
	return toStr(add(x_0, x_0));
}

function f286f(x_0, x_1, x_2)
{
	return concat(x_0, x_2);
}

//@pbe (constraint (= (f799f "404" "xyz") "BxyzAxyz"))
//@pbe (constraint (= (f799f "asdf" "vvvvv") "BvvvvvAvvvvv"))