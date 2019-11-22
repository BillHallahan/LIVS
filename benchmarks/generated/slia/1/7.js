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

function f295f(x_0, x_1)
{
	return len(f893f(x_0, x_1, x_0));
}

//@pbe (constraint (= (f713f "mno pqr st" 9 "404") "81"))
//@pbe (constraint (= (f713f "ab cd" 9 "asdf") "81"))
//@pbe (constraint (= (f713f "404" 8 "asdf") "64"))
//@pbe (constraint (= (f713f "xyz" 2 "xyz") "4"))
//@pbe (constraint (= (f713f "asdf" 6 "xyz") "36"))