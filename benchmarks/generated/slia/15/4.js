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

function f998f(x_0)
{
	return add(x_0, mult(x_0, x_0));
}

function f351f(x_0, x_1, x_2)
{
	return beforeAfter(concat(x_0, x_0));
}

function f532f(x_0, x_1)
{
	return f998f(f998f(x_0));
}

function f543f(x_0, x_1, x_2)
{
	return len(concat(x_0, x_0));
}

//@pbe (constraint (= (f349f 0 "ab cd" "asdf") "Bab cdAab cdab cd"))
//@pbe (constraint (= (f349f 9 "404" "vvvvv") "B404A404404"))