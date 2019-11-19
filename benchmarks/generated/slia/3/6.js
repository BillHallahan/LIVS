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

function f153f(x_0, x_1, x_2)
{
	return toStr(x_1);
}

function f443f(x_0, x_1)
{
	return toStr(mult(x_0, x_0));
}

function f582f(x_0, x_1, x_2)
{
	return toStr(x_0);
}

function f42f(x_0, x_1, x_2)
{
	return toStr(x_0);
}

function f169f(x_0, x_1, x_2)
{
	return mult(x_0, mult(x_0, x_1));
}

function f998f(x_0, x_1)
{
	return beforeAfter(f443f(x_0, x_1));
}

//@pbe (constraint (= (f349f "vvvvv" "hello world" 7) "24"))
//@pbe (constraint (= (f349f "xyz" "404" 6) "22"))