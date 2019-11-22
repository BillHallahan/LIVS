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

//@pbe (constraint (= (f615f 5 "hello world" "mno pqr st") "5B5Bhello worldAA"))
//@pbe (constraint (= (f615f 8 "asdf" "vvvvv") "8B8BasdfAA"))
//@pbe (constraint (= (f615f 10 "hello world" "mno pqr st") "10B10Bhello worldAA"))