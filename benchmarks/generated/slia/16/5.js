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

function f964f(x_0, x_1, x_2)
{
	return len(x_1);
}

function f800f(x_0, x_1)
{
	return len(concat(x_1, x_0));
}

function f785f(x_0, x_1)
{
	return f800f(concat(x_1, x_1), toStr(x_0));
}

function f660f(x_0, x_1, x_2)
{
	return add(x_1, add(x_1, x_1));
}

function f504f(x_0, x_1)
{
	return beforeAfter(x_1);
}

//@pbe (constraint (= (f695f -3 "xyz" "hello world") 3))
//@pbe (constraint (= (f695f 9 "ab cd" "asdf") 5))
//@pbe (constraint (= (f695f 3 "hello world" "hello world") 11))