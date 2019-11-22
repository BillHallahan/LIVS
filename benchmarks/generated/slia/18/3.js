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

function f319f(x_0, x_1, x_2)
{
	return add(mult(x_0, x_0), x_0);
}

function f293f(x_0, x_1, x_2)
{
	return len(x_0);
}

function f918f(x_0, x_1)
{
	return mult(x_1, f319f(x_1, x_0, x_0));
}

//@pbe (constraint (= (f90f "hello world" 4 "hello world") 4352))
//@pbe (constraint (= (f90f "404" 8 "xyz") 266240))
//@pbe (constraint (= (f90f "vvvvv" 5 "xyz") 16250))
//@pbe (constraint (= (f90f "vvvvv" 4 "hello world") 4352))
//@pbe (constraint (= (f90f "asdf" 8 "mno pqr st") 266240))