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

function f824f(x_0, x_1, x_2)
{
	return mult(x_2, x_2);
}

//@pbe (constraint (= (f573f "asdf" 8) 68))
//@pbe (constraint (= (f573f "" -5) 25))
//@pbe (constraint (= (f573f "hello world" -5) 36))
//@pbe (constraint (= (f573f "hello world" 5) 36))