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

function f939f(x_0, x_1)
{
	return f15f(f101f(x_1), f15f(x_1, x_0, x_0), x_0);
}

function f248f(x_0, x_1)
{
	return add(add(x_0, x_1), x_1);
}

function f873f(x_0, x_1, x_2)
{
	return len(beforeAfter(x_2));
}

function f807f(x_0, x_1, x_2)
{
	return mult(add(x_1, x_1), x_1);
}

function f121f(x_0, x_1)
{
	return beforeAfter(x_1);
}

//@pbe (constraint (= (f744f "404" "xyz" -4) "404BxyzA"))
//@pbe (constraint (= (f744f "xyz" "404" -5) "xyzB404A"))
//@pbe (constraint (= (f744f "ab cd" "vvvvv" -3) "ab cdBvvvvvA"))