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

function f755f(x_0, x_1)
{
	return concat(concat(x_0, x_0), concat(x_0, x_0));
}

//@pbe (constraint (= (f593f 2 10 "hello world") "Bhello worldhello worldA"))
//@pbe (constraint (= (f593f 7 4 "asdf") "BasdfasdfA"))
//@pbe (constraint (= (f593f 8 5 "asdf") "BasdfasdfA"))
//@pbe (constraint (= (f593f 9 5 "ab cd") "Bab cdab cdA"))