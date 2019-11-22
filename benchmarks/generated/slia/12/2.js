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

function f58f(x_0, x_1)
{
	return beforeAfter(x_0);
}

//@pbe (constraint (= (f604f "404" 2 10) 32))
//@pbe (constraint (= (f604f "mno pqr st" 1 5) 11))
//@pbe (constraint (= (f604f "vvvvv" 1 9) 19))
//@pbe (constraint (= (f604f "ab cd" 3 0) 3))