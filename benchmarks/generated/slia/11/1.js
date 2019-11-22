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

function f612f(x_0, x_1)
{
	return mult(len(x_1), mult(x_0, x_0));
}

//@pbe (constraint (= (f610f 8 "asdf") 256))
//@pbe (constraint (= (f610f 10 "ab cd") 800))
//@pbe (constraint (= (f610f 7 "hello world") 196))
//@pbe (constraint (= (f610f 8 "asdf") 256))