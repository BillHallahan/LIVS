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

function f183f(x_0)
{
	return beforeAfter(beforeAfter(x_0));
}

//@pbe (constraint (= (f759f "" -2) "BBAA"))
//@pbe (constraint (= (f759f "" -2) "BBAA"))
//@pbe (constraint (= (f759f "hello world" -1) "BBhello worldAA"))