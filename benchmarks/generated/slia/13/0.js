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

//@pbe (constraint (= (f404f "mno pqr st" 8 8) 74))
//@pbe (constraint (= (f404f "hello world" 10 9) 101))
//@pbe (constraint (= (f404f "xyz" 6 6) 39))
//@pbe (constraint (= (f404f "asdf" 4 6) 28))
//@pbe (constraint (= (f404f "mno pqr st" 9 8) 82))