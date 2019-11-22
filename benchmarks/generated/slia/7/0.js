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

//@pbe (constraint (= (f895f 2 7 "mno pqr st") "Bmno pqr stmno pqr stA"))
//@pbe (constraint (= (f895f 0 1 "hello world") "Bhello worldhello worldA"))
//@pbe (constraint (= (f895f 10 1 "asdf") "BasdfasdfA"))
//@pbe (constraint (= (f895f 0 3 "404") "B404404A"))
//@pbe (constraint (= (f895f 0 7 "404") "B404404A"))