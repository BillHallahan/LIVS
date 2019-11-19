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

function f369f(x_0, x_1, x_2)
{
	return add(mult(x_0, x_2), x_2);
}

//@pbe (constraint (= (f222f "ab cd" -2) 0))
//@pbe (constraint (= (f222f "" -1) -1))