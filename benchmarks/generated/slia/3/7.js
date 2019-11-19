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

function f349f(x_0, x_1, x_2)
{
	return toStr(add(x_2, x_2));
}

//@pbe (constraint (= (f911f "404" "vvvvv" -4) -1024))
//@pbe (constraint (= (f911f "asdf" "asdf" -2) -32))
//@pbe (constraint (= (f911f "mno pqr st" "hello world" 0) 0))