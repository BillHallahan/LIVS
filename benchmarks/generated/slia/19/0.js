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

//@pbe (constraint (= (f476f 3 "404" 4) "3"))
//@pbe (constraint (= (f476f 5 "ab cd" 9) "5"))
//@pbe (constraint (= (f476f 10 "404" 0) "10"))
//@pbe (constraint (= (f476f 7 "ab cd" 8) "7"))
//@pbe (constraint (= (f476f 7 "mno pqr st" 9) "7"))