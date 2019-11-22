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

function f562f(x_0, x_1, x_2)
{
	return toStr(x_1);
}

function f507f(x_0, x_1)
{
	return len(x_1);
}

//@pbe (constraint (= (f76f "hello world" "asdf" 4) 331))
//@pbe (constraint (= (f76f "xyz" "mno pqr st" 8) 79))