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

function f781f(x_0)
{
	return toStr(mult(x_0, x_0));
}

function f160f(x_0, x_1)
{
	return f781f(x_0);
}

function f41f(x_0, x_1)
{
	return f160f(mult(x_0, x_0), f160f(x_0, x_1));
}

function f267f(x_0)
{
	return mult(add(x_0, x_0), add(x_0, x_0));
}

function f886f(x_0, x_1, x_2)
{
	return toStr(len(x_0));
}

function f125f(x_0, x_1, x_2)
{
	return beforeAfter(f160f(x_1, x_0));
}

function f382f(x_0, x_1, x_2)
{
	return concat(f781f(x_0), f160f(x_0, x_2));
}

//@pbe (constraint (= (f494f "xyz" 5 "hello world") "Bhello worldxyzA"))
//@pbe (constraint (= (f494f "xyz" 2 "") "BxyzA"))