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

function f381f(x_0, x_1)
{
	return toStr(len(x_0));
}

//@pbe (constraint (= (f779f -1 9) 1))
//@pbe (constraint (= (f779f 1 6) 2))
//@pbe (constraint (= (f779f 3 -3) 2))
//@pbe (constraint (= (f779f 4 -3) 2))