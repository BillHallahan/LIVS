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

function f36f(x_0)
{
	return toStr(x_0);
}

//@pbe (constraint (= (f759f "hello world" 2 "404") "4"))
//@pbe (constraint (= (f759f "mno pqr st" 9 "xyz") "81"))