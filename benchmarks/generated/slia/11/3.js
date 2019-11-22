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

function f612f(x_0, x_1)
{
	return mult(len(x_1), mult(x_0, x_0));
}

function f610f(x_0, x_1)
{
	return f612f(add(x_0, x_0), toStr(x_0));
}

function f338f(x_0, x_1)
{
	return add(mult(x_1, x_1), mult(x_1, x_1));
}

//@pbe (constraint (= (f774f "hello world" "asdf" 8) 65536))
//@pbe (constraint (= (f774f "xyz" "xyz" 5) 10000))
//@pbe (constraint (= (f774f "hello world" "mno pqr st" 5) 10000))
//@pbe (constraint (= (f774f "mno pqr st" "mno pqr st" 1) 16))