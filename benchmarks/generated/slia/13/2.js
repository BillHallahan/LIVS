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

function f404f(x_0, x_1, x_2)
{
	return add(mult(x_2, x_1), len(x_0));
}

function f853f(x_0, x_1, x_2)
{
	return f404f(x_1, add(x_2, x_2), len(x_0));
}

//@pbe (constraint (= (f562f "ab cd" 6 1) "6"))
//@pbe (constraint (= (f562f "ab cd" 7 1) "7"))
//@pbe (constraint (= (f562f "xyz" 3 3) "3"))
//@pbe (constraint (= (f562f "mno pqr st" 4 6) "4"))
//@pbe (constraint (= (f562f "hello world" 7 8) "7"))