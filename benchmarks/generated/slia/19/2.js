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

//@pbe (constraint (= (f221f "asdf" 6) 2))
//@pbe (constraint (= (f221f "" -5) 1))
//@pbe (constraint (= (f221f "mno pqr st" 6) 2))
//@pbe (constraint (= (f221f "xyz" 3) 2))
//@pbe (constraint (= (f221f "hello world" 5) 2))