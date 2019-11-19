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

function f381f(x_0, x_1)
{
	return toStr(len(x_0));
}

function f779f(x_0, x_1)
{
	return len(toStr(x_0));
}

function f838f(x_0, x_1)
{
	return mult(f779f(x_0, x_1), x_1);
}

function f790f(x_0, x_1, x_2)
{
	return beforeAfter(concat(x_2, x_2));
}

function f686f(x_0, x_1)
{
	return mult(add(x_0, x_0), f779f(x_0, x_0));
}

function f905f(x_0, x_1)
{
	return toStr(x_1);
}

function f473f(x_0)
{
	return toStr(x_0);
}

function f580f(x_0)
{
	return mult(add(x_0, x_0), add(x_0, x_0));
}

//@pbe (constraint (= (f701f 5 7) 2))
//@pbe (constraint (= (f701f -4 6) 2))
//@pbe (constraint (= (f701f -3 -1) 1))