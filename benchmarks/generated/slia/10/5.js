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

function f987f(x_0, x_1, x_2)
{
	return len(x_2);
}

function f74f(x_0, x_1)
{
	return concat(x_1, x_1);
}

function f383f(x_0, x_1)
{
	return f74f(f798f(x_1), x_0);
}

//@pbe (constraint (= (f610f -3 "") "BA"))
//@pbe (constraint (= (f610f 4 "asdf") "BasdfAasdf"))
//@pbe (constraint (= (f610f -5 "mno pqr st") "Bmno pqr stAmno pqr st"))
//@pbe (constraint (= (f610f 0 "hello world") "Bhello worldAhello world"))
//@pbe (constraint (= (f610f 9 "mno pqr st") "Bmno pqr stAmno pqr st"))