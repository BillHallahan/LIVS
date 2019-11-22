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

function f164f(x_0, x_1)
{
	return beforeAfter(concat(x_1, x_1));
}

function f594f(x_0, x_1, x_2)
{
	return beforeAfter(f164f(x_2, x_1));
}

function f483f(x_0)
{
	return f164f(mult(x_0, x_0), toStr(x_0));
}

//@pbe (constraint (= (f614f 9 6 "asdf") 54))
//@pbe (constraint (= (f614f 4 0 "hello world") 0))
//@pbe (constraint (= (f614f 0 6 "hello world") 0))
//@pbe (constraint (= (f614f 5 0 "404") 0))
//@pbe (constraint (= (f614f 1 3 "404") 3))