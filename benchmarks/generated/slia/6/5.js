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

function f454f(x_0, x_1, x_2)
{
	return len(concat(x_2, x_2));
}

function f537f(x_0, x_1, x_2)
{
	return f454f(len(x_1), x_0, beforeAfter(x_1));
}

function f858f(x_0, x_1)
{
	return f454f(len(x_1), concat(x_0, x_1), concat(x_0, x_0));
}

function f348f(x_0)
{
	return f858f(toStr(x_0), toStr(x_0));
}

function f155f(x_0, x_1)
{
	return beforeAfter(toStr(x_0));
}

//@pbe (constraint (= (f758f -3 "xyz") "B16A"))
//@pbe (constraint (= (f758f -4 "ab cd") "B20A"))
//@pbe (constraint (= (f758f 1 "xyz") "B16A"))
//@pbe (constraint (= (f758f -4 "ab cd") "B20A"))
//@pbe (constraint (= (f758f 2 "asdf") "B18A"))