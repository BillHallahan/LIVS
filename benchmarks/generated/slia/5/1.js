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

function f829f(x_0, x_1)
{
	return len(concat(x_1, x_1));
}

//@pbe (constraint (= (f321f "vvvvv" "") "10"))
//@pbe (constraint (= (f321f "xyz" "asdf") "14"))
//@pbe (constraint (= (f321f "vvvvv" "ab cd") "15"))