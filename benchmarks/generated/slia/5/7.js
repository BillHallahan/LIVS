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

function f826f(x_0, x_1)
{
	return f829f(f829f(x_1, x_0), x_0);
}

function f477f(x_0, x_1)
{
	return f829f(f829f(x_0, x_1), toStr(x_0));
}

//@pbe (constraint (= (f39f 3 "asdf") 4))
//@pbe (constraint (= (f39f 2 "") 4))
//@pbe (constraint (= (f39f 8 "vvvvv") 6))
//@pbe (constraint (= (f39f 0 "") 4))