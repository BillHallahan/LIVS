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

function f160f(x_0, x_1)
{
	return f781f(x_0);
}

function f41f(x_0, x_1)
{
	return f160f(mult(x_0, x_0), f160f(x_0, x_1));
}

//@pbe (constraint (= (f267f -1) 4))
//@pbe (constraint (= (f267f 6) 144))
//@pbe (constraint (= (f267f 0) 0))
//@pbe (constraint (= (f267f 9) 324))