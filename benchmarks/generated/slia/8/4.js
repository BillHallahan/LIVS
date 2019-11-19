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

function f34f(x_0, x_1, x_2)
{
	return concat(f783f(x_0, x_0, x_2), toStr(x_2));
}

function f937f(x_0)
{
	return mult(x_0, mult(x_0, x_0));
}

function f836f(x_0, x_1, x_2)
{
	return mult(x_2, len(x_1));
}

//@pbe (constraint (= (f425f "vvvvv" 9) "28"))
//@pbe (constraint (= (f425f "asdf" 8) "26"))