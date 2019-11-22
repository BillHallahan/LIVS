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

function f319f(x_0, x_1, x_2)
{
	return add(mult(x_0, x_0), x_0);
}

function f293f(x_0, x_1, x_2)
{
	return len(x_0);
}

function f918f(x_0, x_1)
{
	return mult(x_1, f319f(x_1, x_0, x_0));
}

function f90f(x_0, x_1, x_2)
{
	return f918f(beforeAfter(x_0), mult(x_1, x_1));
}

function f846f(x_0, x_1)
{
	return f293f(beforeAfter(x_0), f90f(x_0, x_1, x_0), x_1);
}

function f500f(x_0, x_1)
{
	return beforeAfter(concat(x_1, x_1));
}

function f176f(x_0, x_1, x_2)
{
	return f319f(mult(x_0, x_2), toStr(x_2), concat(x_1, x_1));
}

//@pbe (constraint (= (f441f 0 "xyz" 4) 0))
//@pbe (constraint (= (f441f 0 "xyz" 8) 0))
//@pbe (constraint (= (f441f 10 "hello world" 2) 4842200))