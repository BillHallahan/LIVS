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

function f799f(x_0, x_1)
{
	return f397f(len(x_0), x_1);
}

function f2f(x_0, x_1)
{
	return f286f(f286f(x_0, x_1, x_0), add(x_1, x_1), f286f(x_0, x_1, x_0));
}

function f276f(x_0, x_1)
{
	return concat(beforeAfter(x_0), beforeAfter(x_0));
}

function f545f(x_0, x_1, x_2)
{
	return add(x_2, mult(x_0, x_2));
}

function f903f(x_0, x_1, x_2)
{
	return f2f(f799f(x_0, x_0), f545f(x_2, x_2, x_2));
}

function f539f(x_0, x_1)
{
	return toStr(len(x_0));
}

//@pbe (constraint (= (f31f 8 "404" "hello world") "B8A"))
//@pbe (constraint (= (f31f 6 "asdf" "vvvvv") "B6A"))
//@pbe (constraint (= (f31f 4 "vvvvv" "xyz") "B4A"))