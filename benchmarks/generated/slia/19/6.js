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

//@pbe (constraint (= (f743f 1 0 "404") "10"))
//@pbe (constraint (= (f743f 4 2 "") "74"))
//@pbe (constraint (= (f743f -5 3 "asdf") "739"))
//@pbe (constraint (= (f743f 8 -2 "404") "74"))