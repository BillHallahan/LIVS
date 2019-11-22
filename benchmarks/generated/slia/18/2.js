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

//@pbe (constraint (= (f918f "xyz" 6) 252))
//@pbe (constraint (= (f918f "asdf" 4) 80))
//@pbe (constraint (= (f918f "xyz" 3) 36))
//@pbe (constraint (= (f918f "404" 9) 810))