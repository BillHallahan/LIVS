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

function f774f(x_0, x_1, x_2)
{
	return mult(f610f(x_2, x_0), f610f(x_2, x_0));
}

function f116f(x_0, x_1, x_2)
{
	return len(toStr(x_1));
}

//@pbe (constraint (= (f122f "mno pqr st" "hello world" 10) "B10A"))
//@pbe (constraint (= (f122f "asdf" "ab cd" 5) "B5A"))
//@pbe (constraint (= (f122f "asdf" "ab cd" 10) "B10A"))
//@pbe (constraint (= (f122f "asdf" "asdf" 3) "B3A"))
//@pbe (constraint (= (f122f "404" "xyz" 8) "B8A"))