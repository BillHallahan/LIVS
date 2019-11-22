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

function f751f(x_0, x_1)
{
	return concat(x_1, beforeAfter(x_1));
}

function f606f(x_0, x_1, x_2)
{
	return concat(beforeAfter(x_1), x_2);
}

function f737f(x_0)
{
	return add(mult(x_0, x_0), mult(x_0, x_0));
}

function f395f(x_0, x_1)
{
	return beforeAfter(x_1);
}

function f189f(x_0)
{
	return toStr(len(x_0));
}

function f129f(x_0, x_1)
{
	return f189f(beforeAfter(x_1));
}

function f693f(x_0)
{
	return toStr(mult(x_0, x_0));
}

//@pbe (constraint (= (f366f 10 9 "vvvvv") "B5A"))
//@pbe (constraint (= (f366f 3 7 "ab cd") "B5A"))
//@pbe (constraint (= (f366f 8 9 "ab cd") "B5A"))
//@pbe (constraint (= (f366f 3 3 "asdf") "B4A"))