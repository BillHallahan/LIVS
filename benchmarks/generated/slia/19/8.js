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

function f624f(x_0, x_1, x_2)
{
	return mult(x_0, mult(x_0, x_0));
}

function f980f(x_0, x_1)
{
	return toStr(len(x_1));
}

function f221f(x_0, x_1)
{
	return len(toStr(x_1));
}

function f483f(x_0, x_1, x_2)
{
	return f980f(add(x_1, x_1), x_0);
}

function f647f(x_0)
{
	return toStr(mult(x_0, x_0));
}

function f762f(x_0, x_1, x_2)
{
	return beforeAfter(f483f(x_2, x_1, x_0));
}

function f743f(x_0, x_1, x_2)
{
	return f647f(f624f(x_1, x_2, x_2));
}

function f127f(x_0, x_1)
{
	return f624f(len(x_1), f980f(x_0, x_1), beforeAfter(x_1));
}

//@pbe (constraint (= (f229f -5 "asdf") "5"))
//@pbe (constraint (= (f229f 5 "xyz") "15"))