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

function f612f(x_0, x_1)
{
	return mult(len(x_1), mult(x_0, x_0));
}

function f610f(x_0, x_1)
{
	return f612f(add(x_0, x_0), toStr(x_0));
}

function f338f(x_0, x_1)
{
	return add(mult(x_1, x_1), mult(x_1, x_1));
}

function f774f(x_0, x_1, x_2)
{
	return mult(f610f(x_2, x_0), f610f(x_2, x_0));
}

//@pbe (constraint (= (f116f "mno pqr st" 8 8) 1))
//@pbe (constraint (= (f116f "vvvvv" 8 2) 1))
//@pbe (constraint (= (f116f "ab cd" 9 2) 1))
//@pbe (constraint (= (f116f "404" 8 3) 1))
//@pbe (constraint (= (f116f "404" 10 9) 2))