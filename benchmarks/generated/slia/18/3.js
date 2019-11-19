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

function f478f(x_0, x_1, x_2)
{
	return beforeAfter(concat(x_1, x_1));
}

function f559f(x_0, x_1, x_2)
{
	return toStr(add(x_1, x_1));
}

function f424f(x_0)
{
	return add(add(x_0, x_0), x_0);
}

//@pbe (constraint (= (f605f "vvvvv" "404") 5))
//@pbe (constraint (= (f605f "mno pqr st" "404") 10))