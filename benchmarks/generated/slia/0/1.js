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

function f781f(x_0)
{
	return toStr(mult(x_0, x_0));
}

//@pbe (constraint (= (f160f -4 "hello world") "26"))
//@pbe (constraint (= (f160f 1 "xyz") "11"))
//@pbe (constraint (= (f160f 8 "xyz") "74"))
//@pbe (constraint (= (f160f 7 "vvvvv") "59"))