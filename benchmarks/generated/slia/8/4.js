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

function f36f(x_0)
{
	return toStr(x_0);
}

function f759f(x_0, x_1, x_2)
{
	return f36f(mult(x_1, x_1));
}

function f916f(x_0)
{
	return f36f(x_0);
}

function f72f(x_0, x_1, x_2)
{
	return toStr(len(x_0));
}

//@pbe (constraint (= (f258f "ab cd" 9 7) "14"))
//@pbe (constraint (= (f258f "ab cd" 2 2) "4"))
//@pbe (constraint (= (f258f "xyz" 6 5) "10"))
//@pbe (constraint (= (f258f "hello world" 0 3) "6"))
//@pbe (constraint (= (f258f "404" 5 10) "20"))