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

function f798f(x_0)
{
	return add(add(x_0, x_0), add(x_0, x_0));
}

function f152f(x_0, x_1, x_2)
{
	return beforeAfter(x_0);
}

//@pbe (constraint (= (f987f -2 4 "mno pqr st") 10))
//@pbe (constraint (= (f987f 6 8 "mno pqr st") 10))
//@pbe (constraint (= (f987f 6 -4 "vvvvv") 5))
//@pbe (constraint (= (f987f 9 8 "mno pqr st") 10))
//@pbe (constraint (= (f987f -4 -1 "asdf") 4))