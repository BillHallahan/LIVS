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

//@pbe (constraint (= (f607f -3 7) 1))
//@pbe (constraint (= (f607f 7 -4) 10))
//@pbe (constraint (= (f607f 2 10) 14))
//@pbe (constraint (= (f607f 6 -2) 10))