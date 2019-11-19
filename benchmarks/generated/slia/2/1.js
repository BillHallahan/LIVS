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

function f482f(x_0)
{
	return beforeAfter(beforeAfter(x_0));
}

//@pbe (constraint (= (f238f -1 "ab cd" "") "Bab cdA"))
//@pbe (constraint (= (f238f 3 "404" "404") "B404A"))
//@pbe (constraint (= (f238f -2 "" "hello world") "BA"))