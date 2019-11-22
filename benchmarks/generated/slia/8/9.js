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

function f36f(x_0)
{
	return toStr(x_0);
}

function f759f(x_0, x_1, x_2)
{
	return f36f(mult(x_1, x_1));
}

function f916f(x_0)
{
	return f36f(x_0);
}

function f72f(x_0, x_1, x_2)
{
	return toStr(len(x_0));
}

function f258f(x_0, x_1, x_2)
{
	return f36f(add(x_2, x_2));
}

function f495f(x_0, x_1, x_2)
{
	return f258f(beforeAfter(x_2), x_1, x_1);
}

function f328f(x_0, x_1)
{
	return concat(f72f(x_1, x_0, x_1), concat(x_1, x_1));
}

function f253f(x_0, x_1)
{
	return mult(mult(x_0, x_0), x_0);
}

function f851f(x_0, x_1, x_2)
{
	return f36f(len(x_2));
}

//@pbe (constraint (= (f985f "xyz" 2) 4))
//@pbe (constraint (= (f985f "hello world" 5) 25))
//@pbe (constraint (= (f985f "404" 3) 9))