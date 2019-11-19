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

//@pbe (constraint (= (f337f -2 "") "BBAA"))
//@pbe (constraint (= (f337f 6 "asdf") "BBasdfasdfAA"))
//@pbe (constraint (= (f337f 10 "404") "BB404404AA"))