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

function f153f(x_0, x_1, x_2)
{
	return toStr(x_1);
}

function f443f(x_0, x_1)
{
	return toStr(mult(x_0, x_0));
}

//@pbe (constraint (= (f582f 3 10 "mno pqr st") "13"))
//@pbe (constraint (= (f582f -5 1 "hello world") "5"))
//@pbe (constraint (= (f582f 8 1 "asdf") "18"))