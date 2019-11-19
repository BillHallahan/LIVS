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

//@pbe (constraint (= (f305f "" 9) "BABA"))
//@pbe (constraint (= (f305f "" 1) "BABA"))
//@pbe (constraint (= (f305f "hello world" -3) "Bhello worldABhello worldA"))