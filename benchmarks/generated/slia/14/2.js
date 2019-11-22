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

function f755f(x_0, x_1)
{
	return concat(concat(x_0, x_0), concat(x_0, x_0));
}

function f593f(x_0, x_1, x_2)
{
	return beforeAfter(concat(x_2, x_2));
}

//@pbe (constraint (= (f356f "404" "mno pqr st" 5) 30))
//@pbe (constraint (= (f356f "asdf" "ab cd" 6) 42))