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

function f829f(x_0, x_1)
{
	return len(concat(x_1, x_1));
}

function f321f(x_0, x_1)
{
	return toStr(len(x_1));
}

function f340f(x_0, x_1)
{
	return f321f(f321f(x_0, x_0), concat(x_0, x_0));
}

//@pbe (constraint (= (f438f -2 3 "hello world") "Bhello worldA"))
//@pbe (constraint (= (f438f 0 1 "404") "B404A"))
//@pbe (constraint (= (f438f -2 -5 "hello world") "Bhello worldA"))