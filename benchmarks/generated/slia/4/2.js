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

function f365f(x_0, x_1, x_2)
{
	return beforeAfter(concat(x_0, x_0));
}

function f337f(x_0, x_1)
{
	return beforeAfter(f365f(x_1, x_0, x_0));
}

//@pbe (constraint (= (f450f 9) 2))
//@pbe (constraint (= (f450f 0) 2))
//@pbe (constraint (= (f450f 6) 2))
//@pbe (constraint (= (f450f -2) 1))
//@pbe (constraint (= (f450f -3) 1))