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

//@pbe (constraint (= (f755f "vvvvv" 0) "vvvvvvvvvvvvvvvvvvvv"))
//@pbe (constraint (= (f755f "404" 4) "404404404404"))
//@pbe (constraint (= (f755f "404" 10) "404404404404"))
//@pbe (constraint (= (f755f "xyz" 9) "xyzxyzxyzxyz"))
//@pbe (constraint (= (f755f "hello world" 9) "hello worldhello worldhello worldhello world"))