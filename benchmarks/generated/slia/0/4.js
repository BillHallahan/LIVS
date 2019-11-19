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

function f781f(x_0)
{
	return toStr(mult(x_0, x_0));
}

function f160f(x_0, x_1)
{
	return f781f(x_0);
}

function f41f(x_0, x_1)
{
	return f160f(mult(x_0, x_0), f160f(x_0, x_1));
}

function f267f(x_0)
{
	return mult(add(x_0, x_0), add(x_0, x_0));
}

//@pbe (constraint (= (f886f "404" 1 -3) "13"))
//@pbe (constraint (= (f886f "vvvvv" 9 8) "15"))
//@pbe (constraint (= (f886f "ab cd" -1 -4) "15"))
//@pbe (constraint (= (f886f "ab cd" 9 6) "15"))