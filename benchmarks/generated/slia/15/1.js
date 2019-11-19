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

function f428f(x_0, x_1, x_2)
{
	return concat(beforeAfter(x_0), concat(x_0, x_1));
}

//@pbe (constraint (= (f697f 6 "asdf") "BasdfAasdf16"))
//@pbe (constraint (= (f697f 4 "vvvvv") "BvvvvvAvvvvv14"))
//@pbe (constraint (= (f697f -5 "") "BA5"))
//@pbe (constraint (= (f697f 5 "404") "B404A40415"))