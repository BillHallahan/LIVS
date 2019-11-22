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

function f798f(x_0, x_1, x_2)
{
	return add(x_2, x_1);
}

function f514f(x_0)
{
	return toStr(mult(x_0, x_0));
}

function f893f(x_0, x_1, x_2)
{
	return f514f(mult(x_1, x_1));
}

//@pbe (constraint (= (f195f 8 "asdf") "65536"))
//@pbe (constraint (= (f195f 9 "hello world") "104976"))
//@pbe (constraint (= (f195f 6 "404") "20736"))
//@pbe (constraint (= (f195f 3 "hello world") "1296"))
//@pbe (constraint (= (f195f 1 "404") "16"))