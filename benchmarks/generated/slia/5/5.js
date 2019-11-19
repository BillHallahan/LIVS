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

function f829f(x_0, x_1)
{
	return len(concat(x_1, x_1));
}

function f321f(x_0, x_1)
{
	return toStr(len(x_1));
}

function f340f(x_0, x_1)
{
	return f321f(f321f(x_0, x_0), concat(x_0, x_0));
}

function f438f(x_0, x_1, x_2)
{
	return beforeAfter(x_2);
}

function f306f(x_0)
{
	return mult(add(x_0, x_0), x_0);
}

//@pbe (constraint (= (f826f "mno pqr st" 7) 20))
//@pbe (constraint (= (f826f "xyz" 5) 6))
//@pbe (constraint (= (f826f "ab cd" -3) 10))
//@pbe (constraint (= (f826f "" -3) 0))