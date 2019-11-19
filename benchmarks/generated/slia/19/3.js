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

function f624f(x_0, x_1, x_2)
{
	return mult(x_0, mult(x_0, x_0));
}

function f980f(x_0, x_1)
{
	return toStr(len(x_1));
}

function f221f(x_0, x_1)
{
	return len(toStr(x_1));
}

//@pbe (constraint (= (f483f "hello world" -3 "404") "21"))
//@pbe (constraint (= (f483f "" 2 "hello world") "10"))
//@pbe (constraint (= (f483f "xyz" 8 "ab cd") "13"))
//@pbe (constraint (= (f483f "mno pqr st" 4 "asdf") "20"))
//@pbe (constraint (= (f483f "hello world" -2 "") "21"))