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

function f482f(x_0)
{
	return beforeAfter(beforeAfter(x_0));
}

function f238f(x_0, x_1, x_2)
{
	return beforeAfter(x_1);
}

function f866f(x_0, x_1, x_2)
{
	return f238f(x_0, concat(x_2, x_2), concat(x_2, x_2));
}

function f693f(x_0, x_1)
{
	return len(concat(x_1, x_1));
}

function f294f(x_0, x_1, x_2)
{
	return f238f(f693f(x_2, x_0), toStr(x_1), beforeAfter(x_0));
}

function f488f(x_0, x_1, x_2)
{
	return f294f(x_2, mult(x_1, x_1), x_1);
}

function f557f(x_0, x_1, x_2)
{
	return toStr(f693f(x_1, x_0));
}

function f427f(x_0, x_1, x_2)
{
	return f482f(f294f(x_2, x_0, x_1));
}

function f702f(x_0)
{
	return len(concat(x_0, x_0));
}

//@pbe (constraint (= (f463f -5 "xyz") 16))
//@pbe (constraint (= (f463f -4 "404") 16))
//@pbe (constraint (= (f463f 6 "404") 16))