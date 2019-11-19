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

//@pbe (constraint (= (f624f 0 "vvvvv" "vvvvv") 0))
//@pbe (constraint (= (f624f 5 "404" "vvvvv") 125))
//@pbe (constraint (= (f624f -1 "ab cd" "ab cd") -1))
//@pbe (constraint (= (f624f 0 "404" "xyz") 0))