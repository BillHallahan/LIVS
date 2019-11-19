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

function f530f(x_0, x_1, x_2)
{
	return mult(mult(x_1, x_1), mult(x_1, x_1));
}

//@pbe (constraint (= (f503f 7 "") "BA"))
//@pbe (constraint (= (f503f 1 "404") "404B404A"))
//@pbe (constraint (= (f503f 5 "mno pqr st") "mno pqr stBmno pqr stA"))