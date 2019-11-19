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

function f15f(x_0, x_1, x_2)
{
	return beforeAfter(x_2);
}

function f101f(x_0)
{
	return mult(mult(x_0, x_0), mult(x_0, x_0));
}

function f507f(x_0, x_1, x_2)
{
	return toStr(f101f(x_1));
}

//@pbe (constraint (= (f939f "xyz" 10) "BxyzA"))
//@pbe (constraint (= (f939f "vvvvv" -1) "BvvvvvA"))
//@pbe (constraint (= (f939f "vvvvv" -2) "BvvvvvA"))
//@pbe (constraint (= (f939f "mno pqr st" -2) "Bmno pqr stA"))