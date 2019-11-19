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

function f381f(x_0, x_1)
{
	return toStr(len(x_0));
}

function f779f(x_0, x_1)
{
	return len(toStr(x_0));
}

function f838f(x_0, x_1)
{
	return mult(f779f(x_0, x_1), x_1);
}

//@pbe (constraint (= (f790f 6 "ab cd" "404") "B404404A"))
//@pbe (constraint (= (f790f 8 "vvvvv" "hello world") "Bhello worldhello worldA"))
//@pbe (constraint (= (f790f 4 "xyz" "asdf") "BasdfasdfA"))
//@pbe (constraint (= (f790f 9 "hello world" "404") "B404404A"))