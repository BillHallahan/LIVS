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

//@pbe (constraint (= (f397f 6 "asdf") "BasdfAasdf"))
//@pbe (constraint (= (f397f 6 "hello world") "Bhello worldAhello world"))
//@pbe (constraint (= (f397f 7 "xyz") "BxyzAxyz"))