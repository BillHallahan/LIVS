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

//@pbe (constraint (= (f164f 8 "mno pqr st") "Bmno pqr stmno pqr stA"))
//@pbe (constraint (= (f164f 9 "mno pqr st") "Bmno pqr stmno pqr stA"))
//@pbe (constraint (= (f164f 7 "hello world") "Bhello worldhello worldA"))
//@pbe (constraint (= (f164f 4 "xyz") "BxyzxyzA"))