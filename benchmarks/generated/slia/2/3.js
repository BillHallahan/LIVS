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

function f482f(x_0)
{
	return beforeAfter(beforeAfter(x_0));
}

function f238f(x_0, x_1, x_2)
{
	return beforeAfter(x_1);
}

function f866f(x_0, x_1, x_2)
{
	return f238f(x_0, concat(x_2, x_2), concat(x_2, x_2));
}

//@pbe (constraint (= (f693f 7 "asdf") 8))
//@pbe (constraint (= (f693f 5 "vvvvv") 10))