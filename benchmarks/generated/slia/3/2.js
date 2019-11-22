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

function f397f(x_0, x_1)
{
	return concat(beforeAfter(x_1), x_1);
}

function f43f(x_0)
{
	return toStr(add(x_0, x_0));
}

//@pbe (constraint (= (f286f "vvvvv" 3 "asdf") "vvvvvasdf"))
//@pbe (constraint (= (f286f "vvvvv" 5 "vvvvv") "vvvvvvvvvv"))
//@pbe (constraint (= (f286f "xyz" 7 "mno pqr st") "xyzmno pqr st"))
//@pbe (constraint (= (f286f "vvvvv" 1 "asdf") "vvvvvasdf"))
//@pbe (constraint (= (f286f "vvvvv" 8 "hello world") "vvvvvhello world"))