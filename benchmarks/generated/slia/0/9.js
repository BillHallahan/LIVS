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

function f703f(x_0, x_1, x_2)
{
	return len(x_1);
}

function f339f(x_0, x_1, x_2)
{
	return concat(f897f(x_0, x_2), f897f(x_1, x_2));
}

//@pbe (constraint (= (f826f "404" 6) "BBB404404AB404404AAA"))
//@pbe (constraint (= (f826f "404" 7) "BBB404404AB404404AAA"))
//@pbe (constraint (= (f826f "mno pqr st" 4) "BBBmno pqr stmno pqr stABmno pqr stmno pqr stAAA"))