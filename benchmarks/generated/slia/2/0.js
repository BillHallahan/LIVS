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

//@pbe (constraint (= (f482f "") "BBAA"))
//@pbe (constraint (= (f482f "xyz") "BBxyzAA"))
//@pbe (constraint (= (f482f "404") "BB404AA"))
//@pbe (constraint (= (f482f "hello world") "BBhello worldAA"))