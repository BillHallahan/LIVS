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

function f381f(x_0, x_1)
{
	return toStr(len(x_0));
}

function f779f(x_0, x_1)
{
	return len(toStr(x_0));
}

function f838f(x_0, x_1)
{
	return mult(f779f(x_0, x_1), x_1);
}

function f790f(x_0, x_1, x_2)
{
	return beforeAfter(concat(x_2, x_2));
}

//@pbe (constraint (= (f686f 9 "xyz") 36))
//@pbe (constraint (= (f686f -1 "vvvvv") -2))
//@pbe (constraint (= (f686f 5 "xyz") 20))
//@pbe (constraint (= (f686f -4 "ab cd") -8))
//@pbe (constraint (= (f686f 1 "vvvvv") 4))