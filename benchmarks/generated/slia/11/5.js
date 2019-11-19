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

function f983f(x_0, x_1)
{
	return add(add(x_0, x_0), x_0);
}

function f134f(x_0, x_1, x_2)
{
	return concat(beforeAfter(x_1), toStr(x_2));
}

//@pbe (constraint (= (f705f "hello world" "vvvvv" 2) "B12A12"))
//@pbe (constraint (= (f705f "404" "vvvvv" 6) "B16A16"))
//@pbe (constraint (= (f705f "404" "asdf" -3) "B7A7"))