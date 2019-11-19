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

function f363f(x_0, x_1)
{
	return beforeAfter(concat(x_1, x_1));
}

//@pbe (constraint (= (f339f "vvvvv" -4) -16))
//@pbe (constraint (= (f339f "vvvvv" 0) 0))
//@pbe (constraint (= (f339f "mno pqr st" 7) 28))
//@pbe (constraint (= (f339f "xyz" -3) -12))
//@pbe (constraint (= (f339f "xyz" 5) 20))