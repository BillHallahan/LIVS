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

//@pbe (constraint (= (f189f "xyz") "3"))
//@pbe (constraint (= (f189f "hello world") "11"))
//@pbe (constraint (= (f189f "xyz") "3"))
//@pbe (constraint (= (f189f "xyz") "3"))