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

function f478f(x_0, x_1, x_2)
{
	return beforeAfter(concat(x_1, x_1));
}

function f559f(x_0, x_1, x_2)
{
	return toStr(add(x_1, x_1));
}

function f424f(x_0)
{
	return add(add(x_0, x_0), x_0);
}

function f605f(x_0, x_1)
{
	return len(x_0);
}

function f62f(x_0, x_1, x_2)
{
	return f424f(f424f(x_2));
}

function f465f(x_0, x_1)
{
	return f424f(x_1);
}

function f426f(x_0)
{
	return beforeAfter(x_0);
}

//@pbe (constraint (= (f694f 6 "404") 6))
//@pbe (constraint (= (f694f 3 "hello world") 22))