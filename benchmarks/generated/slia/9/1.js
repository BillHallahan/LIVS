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

function f728f(x_0, x_1, x_2)
{
	return add(len(x_0), add(x_2, x_2));
}

//@pbe (constraint (= (f803f "mno pqr st" 2) 16))
//@pbe (constraint (= (f803f "vvvvv" 0) 7))
//@pbe (constraint (= (f803f "hello world" 0) 13))