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

function f428f(x_0, x_1, x_2)
{
	return concat(beforeAfter(x_0), concat(x_0, x_1));
}

function f697f(x_0, x_1)
{
	return f428f(x_1, toStr(x_0), len(x_1));
}

//@pbe (constraint (= (f24f "mno pqr st" 2 9) "Bmno pqr stAmno pqr st19Bmno pqr stAmno pqr st12"))
//@pbe (constraint (= (f24f "" -5 4) "BA14BA5"))
//@pbe (constraint (= (f24f "vvvvv" 6 -2) "BvvvvvAvvvvv8BvvvvvAvvvvv16"))
//@pbe (constraint (= (f24f "vvvvv" 9 -1) "BvvvvvAvvvvv9BvvvvvAvvvvv19"))
//@pbe (constraint (= (f24f "vvvvv" 1 -5) "BvvvvvAvvvvv5BvvvvvAvvvvv11"))