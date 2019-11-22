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

function f476f(x_0, x_1, x_2)
{
	return toStr(x_0);
}

function f283f(x_0, x_1, x_2)
{
	return concat(f476f(x_2, x_0, x_2), beforeAfter(x_0));
}

function f868f(x_0, x_1)
{
	return len(toStr(x_0));
}

function f615f(x_0, x_1, x_2)
{
	return f283f(f283f(x_1, x_0, x_0), f868f(x_0, x_0), x_0);
}

function f655f(x_0)
{
	return len(toStr(x_0));
}

//@pbe (constraint (= (f127f 10 "mno pqr st") "2"))
//@pbe (constraint (= (f127f 10 "asdf") "2"))
//@pbe (constraint (= (f127f 5 "asdf") "1"))
//@pbe (constraint (= (f127f 6 "vvvvv") "1"))
//@pbe (constraint (= (f127f 10 "vvvvv") "2"))