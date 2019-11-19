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

//@pbe (constraint (= (f183f "") "BBAA"))
//@pbe (constraint (= (f183f "mno pqr st") "BBmno pqr stAA"))
//@pbe (constraint (= (f183f "ab cd") "BBab cdAA"))
//@pbe (constraint (= (f183f "ab cd") "BBab cdAA"))