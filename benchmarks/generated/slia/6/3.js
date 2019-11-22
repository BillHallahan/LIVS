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
	return x_0 + "";
}

function beforeAfter(x_0)
{
	return 'B' + x_0 + 'A';
}

function f950f(x_0, x_1, x_2)
{
	return beforeAfter(x_1);
}

function f75f(x_0, x_1, x_2)
{
	return add(add(x_1, x_1), add(x_0, x_0));
}

function f314f(x_0, x_1)
{
	return toStr(len(x_0));
}

//@pbe (constraint (= (f844f "asdf" "asdf" 8) 48))
//@pbe (constraint (= (f844f "ab cd" "asdf" 3) 18))