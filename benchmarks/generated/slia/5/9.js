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

function f696f(x_0)
{
	return mult(mult(x_0, x_0), x_0);
}

function f405f(x_0, x_1, x_2)
{
	return len(concat(x_2, x_0));
}

function f213f(x_0)
{
	return concat(beforeAfter(x_0), x_0);
}

function f684f(x_0, x_1, x_2)
{
	return concat(x_0, beforeAfter(x_0));
}

function f130f(x_0, x_1, x_2)
{
	return len(f213f(x_2));
}

function f585f(x_0, x_1)
{
	return toStr(add(x_1, x_0));
}

function f384f(x_0, x_1, x_2)
{
	return f130f(f585f(x_2, x_2), f405f(x_0, x_1, x_0), f585f(x_2, x_1));
}

function f348f(x_0)
{
	return toStr(len(x_0));
}

function f889f(x_0, x_1)
{
	return toStr(f405f(x_1, x_0, x_1));
}

//@pbe (constraint (= (f418f "404" 5) "B404B404AA"))
//@pbe (constraint (= (f418f "404" 0) "B404B404AA"))
//@pbe (constraint (= (f418f "ab cd" 10) "Bab cdBab cdAA"))