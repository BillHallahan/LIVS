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

function f798f(x_0, x_1, x_2)
{
	return add(x_2, x_1);
}

function f514f(x_0)
{
	return toStr(mult(x_0, x_0));
}

function f893f(x_0, x_1, x_2)
{
	return f514f(mult(x_1, x_1));
}

function f195f(x_0, x_1)
{
	return f893f(toStr(x_0), f798f(x_0, x_0, x_0), f893f(x_1, x_0, x_1));
}

function f613f(x_0, x_1, x_2)
{
	return f798f(f798f(x_2, x_1, x_1), f798f(x_1, x_2, x_2), x_1);
}

function f809f(x_0, x_1)
{
	return toStr(x_1);
}

//@pbe (constraint (= (f295f "xyz" 2) 2))
//@pbe (constraint (= (f295f "mno pqr st" 9) 4))