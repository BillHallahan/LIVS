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

function f15f(x_0, x_1, x_2)
{
	return beforeAfter(x_2);
}

function f101f(x_0)
{
	return mult(mult(x_0, x_0), mult(x_0, x_0));
}

function f507f(x_0, x_1, x_2)
{
	return toStr(f101f(x_1));
}

function f939f(x_0, x_1)
{
	return f15f(f101f(x_1), f15f(x_1, x_0, x_0), x_0);
}

function f248f(x_0, x_1)
{
	return add(add(x_0, x_1), x_1);
}

//@pbe (constraint (= (f873f 8 6 "asdf") 6))
//@pbe (constraint (= (f873f 6 -2 "") 2))
//@pbe (constraint (= (f873f 6 -5 "asdf") 6))
//@pbe (constraint (= (f873f -5 7 "asdf") 6))