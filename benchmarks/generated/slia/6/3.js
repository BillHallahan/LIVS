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

//@pbe (constraint (= (f348f 4) 8))
//@pbe (constraint (= (f348f -1) 4))
//@pbe (constraint (= (f348f 8) 8))