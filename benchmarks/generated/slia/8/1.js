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

function f783f(x_0, x_1, x_2)
{
	return toStr(add(x_2, x_2));
}

//@pbe (constraint (= (f34f "ab cd" -3 3) "1613"))
//@pbe (constraint (= (f34f "xyz" 1 0) "1010"))