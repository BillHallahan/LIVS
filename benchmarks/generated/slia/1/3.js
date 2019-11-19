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

function f530f(x_0, x_1, x_2)
{
	return mult(mult(x_1, x_1), mult(x_1, x_1));
}

function f503f(x_0, x_1)
{
	return concat(x_1, beforeAfter(x_1));
}

function f609f(x_0, x_1)
{
	return f530f(beforeAfter(x_1), f530f(x_1, x_0, x_1), f503f(x_0, x_1));
}

//@pbe (constraint (= (f57f "ab cd" 6) 12))
//@pbe (constraint (= (f57f "xyz" -3) 8))
//@pbe (constraint (= (f57f "mno pqr st" 6) 22))
//@pbe (constraint (= (f57f "hello world" 3) 24))
//@pbe (constraint (= (f57f "vvvvv" 0) 12))