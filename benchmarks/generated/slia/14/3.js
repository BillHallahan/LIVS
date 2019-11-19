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

function f952f(x_0, x_1, x_2)
{
	return beforeAfter(toStr(x_1));
}

function f972f(x_0, x_1, x_2)
{
	return beforeAfter(x_1);
}

function f305f(x_0, x_1)
{
	return concat(beforeAfter(x_0), beforeAfter(x_0));
}

//@pbe (constraint (= (f639f "mno pqr st" -2 "vvvvv") 24))
//@pbe (constraint (= (f639f "vvvvv" 7 "hello world") 14))
//@pbe (constraint (= (f639f "vvvvv" 7 "hello world") 14))