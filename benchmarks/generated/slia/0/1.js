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

function f164f(x_0, x_1)
{
	return beforeAfter(concat(x_1, x_1));
}

//@pbe (constraint (= (f594f 6 "404" 5) "BB404404AA"))
//@pbe (constraint (= (f594f 6 "mno pqr st" 0) "BBmno pqr stmno pqr stAA"))
//@pbe (constraint (= (f594f 7 "asdf" 10) "BBasdfasdfAA"))
//@pbe (constraint (= (f594f 9 "asdf" 8) "BBasdfasdfAA"))