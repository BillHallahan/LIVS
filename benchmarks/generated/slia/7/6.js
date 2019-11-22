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

function f352f(x_0)
{
	return toStr(mult(x_0, x_0));
}

function f266f(x_0, x_1, x_2)
{
	return beforeAfter(toStr(x_1));
}

function f586f(x_0, x_1, x_2)
{
	return add(x_2, len(x_1));
}

function f177f(x_0, x_1)
{
	return toStr(f586f(x_1, x_1, x_0));
}

function f961f(x_0, x_1)
{
	return toStr(mult(x_1, x_1));
}

//@pbe (constraint (= (f277f 4 "hello world") "16"))
//@pbe (constraint (= (f277f 1 "mno pqr st") "1"))
//@pbe (constraint (= (f277f 3 "hello world") "9"))