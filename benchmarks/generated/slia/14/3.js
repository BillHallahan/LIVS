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

function f356f(x_0, x_1, x_2)
{
	return add(x_2, mult(x_2, x_2));
}

//@pbe (constraint (= (f470f 5 "mno pqr st" 2) 20))
//@pbe (constraint (= (f470f 3 "hello world" 10) 10100))
//@pbe (constraint (= (f470f 1 "404" 7) 2450))
//@pbe (constraint (= (f470f 10 "asdf" 3) 90))
//@pbe (constraint (= (f470f 3 "mno pqr st" 10) 10100))