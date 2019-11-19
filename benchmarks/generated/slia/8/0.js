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

//@pbe (constraint (= (f783f "xyz" "vvvvv" 2) "14"))
//@pbe (constraint (= (f783f "mno pqr st" "ab cd" 3) "16"))
//@pbe (constraint (= (f783f "vvvvv" "404" 8) "26"))