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

//@pbe (constraint (= (f381f "vvvvv" "404") "15"))
//@pbe (constraint (= (f381f "ab cd" "mno pqr st") "15"))
//@pbe (constraint (= (f381f "404" "mno pqr st") "13"))
//@pbe (constraint (= (f381f "xyz" "vvvvv") "13"))