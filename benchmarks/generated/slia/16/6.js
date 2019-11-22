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

function f115f(x_0, x_1, x_2)
{
	return len(concat(x_2, x_0));
}

function f487f(x_0)
{
	return f184f(concat(x_0, x_0), beforeAfter(x_0));
}

function f381f(x_0, x_1)
{
	return len(toStr(x_0));
}

function f842f(x_0, x_1, x_2)
{
	return f399f(concat(x_0, x_0), concat(x_2, x_0), add(x_1, x_1));
}

//@pbe (constraint (= (f949f "404" "vvvvv" 9) 14))
//@pbe (constraint (= (f949f "404" "xyz" 4) 10))
//@pbe (constraint (= (f949f "xyz" "ab cd" 4) 14))
//@pbe (constraint (= (f949f "ab cd" "hello world" 3) 26))
//@pbe (constraint (= (f949f "asdf" "404" 4) 10))