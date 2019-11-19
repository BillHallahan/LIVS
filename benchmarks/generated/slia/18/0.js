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

//@pbe (constraint (= (f478f 0 "vvvvv" 0) "BvvvvvvvvvvA"))
//@pbe (constraint (= (f478f 7 "asdf" 1) "BasdfasdfA"))
//@pbe (constraint (= (f478f -5 "asdf" -5) "BasdfasdfA"))