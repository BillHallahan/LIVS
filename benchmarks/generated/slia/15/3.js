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

function f998f(x_0)
{
	return add(x_0, mult(x_0, x_0));
}

function f351f(x_0, x_1, x_2)
{
	return beforeAfter(concat(x_0, x_0));
}

function f532f(x_0, x_1)
{
	return f998f(f998f(x_0));
}

//@pbe (constraint (= (f543f "mno pqr st" "asdf" 9) 20))
//@pbe (constraint (= (f543f "hello world" "vvvvv" 4) 22))
//@pbe (constraint (= (f543f "hello world" "xyz" 2) 22))
//@pbe (constraint (= (f543f "asdf" "ab cd" 4) 8))
//@pbe (constraint (= (f543f "asdf" "404" 5) 8))