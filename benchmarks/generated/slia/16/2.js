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

function f184f(x_0, x_1)
{
	return mult(len(x_1), len(x_0));
}

function f399f(x_0, x_1, x_2)
{
	return toStr(add(x_2, x_2));
}

//@pbe (constraint (= (f115f "ab cd" "hello world" "ab cd") 10))
//@pbe (constraint (= (f115f "asdf" "asdf" "vvvvv") 9))
//@pbe (constraint (= (f115f "404" "xyz" "vvvvv") 8))
//@pbe (constraint (= (f115f "404" "asdf" "xyz") 6))
//@pbe (constraint (= (f115f "asdf" "vvvvv" "asdf") 8))