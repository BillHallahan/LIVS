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

function f277f(x_0, x_1)
{
	return f352f(x_0);
}

function f548f(x_0, x_1, x_2)
{
	return len(beforeAfter(x_0));
}

function f966f(x_0)
{
	return concat(x_0, concat(x_0, x_0));
}

//@pbe (constraint (= (f568f 7) "49"))
//@pbe (constraint (= (f568f 1) "1"))
//@pbe (constraint (= (f568f 6) "36"))
//@pbe (constraint (= (f568f 8) "64"))
//@pbe (constraint (= (f568f 6) "36"))