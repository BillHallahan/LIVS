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

function f15f(x_0, x_1, x_2)
{
	return beforeAfter(x_2);
}

function f101f(x_0)
{
	return mult(mult(x_0, x_0), mult(x_0, x_0));
}

//@pbe (constraint (= (f507f 8 4 7) "266"))
//@pbe (constraint (= (f507f 2 2 -4) "26"))
//@pbe (constraint (= (f507f -5 -4 -3) "266"))
//@pbe (constraint (= (f507f 10 -4 -3) "266"))
//@pbe (constraint (= (f507f 0 -4 7) "266"))