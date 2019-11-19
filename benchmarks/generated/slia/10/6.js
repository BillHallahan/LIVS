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

function f610f(x_0, x_1)
{
	return concat(beforeAfter(x_1), x_1);
}

//@pbe (constraint (= (f10f "404" 4 "404") "BB404A404A"))
//@pbe (constraint (= (f10f "404" -1 "ab cd") "BBab cdAab cdA"))
//@pbe (constraint (= (f10f "xyz" 8 "") "BBAA"))
//@pbe (constraint (= (f10f "hello world" 10 "mno pqr st") "BBmno pqr stAmno pqr stA"))