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

function f164f(x_0, x_1)
{
	return beforeAfter(concat(x_1, x_1));
}

function f594f(x_0, x_1, x_2)
{
	return beforeAfter(f164f(x_2, x_1));
}

function f483f(x_0)
{
	return f164f(mult(x_0, x_0), toStr(x_0));
}

function f614f(x_0, x_1, x_2)
{
	return mult(x_1, x_0);
}

function f761f(x_0, x_1, x_2)
{
	return len(toStr(x_1));
}

function f230f(x_0, x_1, x_2)
{
	return f761f(mult(x_0, x_0), add(x_0, x_0), x_1);
}

//@pbe (constraint (= (f897f 6 "asdf") "BB66AA"))
//@pbe (constraint (= (f897f 1 "404") "BB11AA"))
//@pbe (constraint (= (f897f 1 "mno pqr st") "BB11AA"))
//@pbe (constraint (= (f897f 5 "mno pqr st") "BB55AA"))
//@pbe (constraint (= (f897f 5 "ab cd") "BB55AA"))