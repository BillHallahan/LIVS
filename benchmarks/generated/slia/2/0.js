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

//@pbe (constraint (= (f751f 1 "xyz") "xyzBxyzA"))
//@pbe (constraint (= (f751f 1 "xyz") "xyzBxyzA"))
//@pbe (constraint (= (f751f 5 "404") "404B404A"))