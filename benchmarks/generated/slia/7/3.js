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

function f895f(x_0, x_1, x_2)
{
	return beforeAfter(concat(x_2, x_2));
}

function f352f(x_0)
{
	return toStr(mult(x_0, x_0));
}

function f266f(x_0, x_1, x_2)
{
	return beforeAfter(toStr(x_1));
}

//@pbe (constraint (= (f586f "hello world" "ab cd" 8) 13))
//@pbe (constraint (= (f586f "hello world" "asdf" 0) 4))
//@pbe (constraint (= (f586f "404" "mno pqr st" 8) 18))
//@pbe (constraint (= (f586f "mno pqr st" "asdf" 7) 11))