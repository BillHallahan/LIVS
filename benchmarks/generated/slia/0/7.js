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

function f897f(x_0, x_1)
{
	return beforeAfter(f483f(x_0));
}

//@pbe (constraint (= (f703f 1 "xyz" 0) 3))
//@pbe (constraint (= (f703f 2 "mno pqr st" 3) 10))
//@pbe (constraint (= (f703f 8 "asdf" 3) 4))
//@pbe (constraint (= (f703f 8 "mno pqr st" 2) 10))