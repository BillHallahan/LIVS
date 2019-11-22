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

//@pbe (constraint (= (f737f 6) 72))
//@pbe (constraint (= (f737f 10) 200))
//@pbe (constraint (= (f737f 6) 72))
//@pbe (constraint (= (f737f 0) 0))
//@pbe (constraint (= (f737f 2) 8))