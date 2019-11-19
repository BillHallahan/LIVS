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

function f153f(x_0, x_1, x_2)
{
	return toStr(x_1);
}

function f443f(x_0, x_1)
{
	return toStr(mult(x_0, x_0));
}

function f582f(x_0, x_1, x_2)
{
	return toStr(x_0);
}

//@pbe (constraint (= (f42f -1 7 -2) "9"))
//@pbe (constraint (= (f42f -4 -3 -2) "6"))
//@pbe (constraint (= (f42f 1 7 9) "11"))
//@pbe (constraint (= (f42f 7 -5 5) "17"))
//@pbe (constraint (= (f42f -1 -1 10) "9"))