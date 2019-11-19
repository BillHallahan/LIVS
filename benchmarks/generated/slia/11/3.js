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

function f369f(x_0, x_1, x_2)
{
	return add(mult(x_0, x_2), x_2);
}

function f222f(x_0, x_1)
{
	return add(mult(x_1, x_1), add(x_1, x_1));
}

function f135f(x_0, x_1, x_2)
{
	return mult(f369f(x_0, x_2, x_0), add(x_0, x_0));
}

//@pbe (constraint (= (f983f 10 "ab cd") 30))
//@pbe (constraint (= (f983f 0 "mno pqr st") 0))