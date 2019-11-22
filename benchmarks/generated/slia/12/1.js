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

function f272f(x_0, x_1, x_2)
{
	return add(x_0, add(x_0, x_0));
}

//@pbe (constraint (= (f58f "vvvvv" "xyz") "BvvvvvA"))
//@pbe (constraint (= (f58f "asdf" "ab cd") "BasdfA"))
//@pbe (constraint (= (f58f "hello world" "ab cd") "Bhello worldA"))
//@pbe (constraint (= (f58f "vvvvv" "vvvvv") "BvvvvvA"))
//@pbe (constraint (= (f58f "vvvvv" "mno pqr st") "BvvvvvA"))