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

function f428f(x_0, x_1, x_2)
{
	return concat(beforeAfter(x_0), concat(x_0, x_1));
}

function f697f(x_0, x_1)
{
	return f428f(x_1, toStr(x_0), len(x_1));
}

function f24f(x_0, x_1, x_2)
{
	return concat(f697f(x_2, x_0), f697f(x_1, x_0));
}

function f576f(x_0, x_1, x_2)
{
	return beforeAfter(concat(x_0, x_0));
}

function f388f(x_0, x_1, x_2)
{
	return mult(len(x_0), mult(x_2, x_2));
}

function f690f(x_0, x_1)
{
	return f428f(f697f(x_0, x_1), f428f(x_1, x_1, x_0), mult(x_0, x_0));
}

//@pbe (constraint (= (f717f "vvvvv") "15"))
//@pbe (constraint (= (f717f "404") "13"))
//@pbe (constraint (= (f717f "hello world") "21"))
//@pbe (constraint (= (f717f "xyz") "13"))
//@pbe (constraint (= (f717f "xyz") "13"))