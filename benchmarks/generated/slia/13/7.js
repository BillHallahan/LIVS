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

function f76f(x_0, x_1, x_2)
{
	return f853f(concat(x_1, x_0), f562f(x_0, x_2, x_2), len(x_0));
}

function f522f(x_0)
{
	return mult(f507f(x_0, x_0), len(x_0));
}

function f836f(x_0, x_1)
{
	return mult(f507f(x_0, x_0), f507f(x_0, x_0));
}

//@pbe (constraint (= (f718f 2 "vvvvv") 1))
//@pbe (constraint (= (f718f 10 "ab cd") 4))
//@pbe (constraint (= (f718f 4 "404") 1))
//@pbe (constraint (= (f718f 10 "mno pqr st") 4))