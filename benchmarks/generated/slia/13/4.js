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

function f183f(x_0)
{
	return beforeAfter(beforeAfter(x_0));
}

function f759f(x_0, x_1)
{
	return f183f(x_0);
}

function f565f(x_0, x_1, x_2)
{
	return add(x_2, x_2);
}

function f684f(x_0, x_1, x_2)
{
	return concat(x_0, x_1);
}

//@pbe (constraint (= (f835f 9 "ab cd" "ab cd") "BBBab cdAAA"))
//@pbe (constraint (= (f835f -1 "" "xyz") "BBBAAA"))
//@pbe (constraint (= (f835f 10 "mno pqr st" "vvvvv") "BBBmno pqr stAAA"))
//@pbe (constraint (= (f835f 0 "404" "mno pqr st") "BBB404AAA"))