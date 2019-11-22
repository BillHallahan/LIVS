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

function f895f(x_0, x_1, x_2)
{
	return beforeAfter(concat(x_2, x_2));
}

//@pbe (constraint (= (f352f 7) "49"))
//@pbe (constraint (= (f352f 2) "4"))
//@pbe (constraint (= (f352f 0) "0"))
//@pbe (constraint (= (f352f 8) "64"))