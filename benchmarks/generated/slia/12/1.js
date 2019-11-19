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

function f607f(x_0, x_1)
{
	return add(x_1, add(x_0, x_0));
}

//@pbe (constraint (= (f363f "404" "ab cd") "Bab cdab cdA"))
//@pbe (constraint (= (f363f "ab cd" "vvvvv") "BvvvvvvvvvvA"))
//@pbe (constraint (= (f363f "mno pqr st" "vvvvv") "BvvvvvvvvvvA"))
//@pbe (constraint (= (f363f "xyz" "ab cd") "Bab cdab cdA"))