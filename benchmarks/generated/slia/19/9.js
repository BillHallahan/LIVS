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

function f476f(x_0, x_1, x_2)
{
	return toStr(x_0);
}

function f283f(x_0, x_1, x_2)
{
	return concat(f476f(x_2, x_0, x_2), beforeAfter(x_0));
}

function f868f(x_0, x_1)
{
	return len(toStr(x_0));
}

function f615f(x_0, x_1, x_2)
{
	return f283f(f283f(x_1, x_0, x_0), f868f(x_0, x_0), x_0);
}

function f655f(x_0)
{
	return len(toStr(x_0));
}

function f127f(x_0, x_1)
{
	return toStr(f868f(x_0, x_0));
}

function f173f(x_0, x_1, x_2)
{
	return f868f(x_1, x_2);
}

function f709f(x_0)
{
	return beforeAfter(beforeAfter(x_0));
}

function f679f(x_0, x_1, x_2)
{
	return f283f(x_1, f655f(x_0), x_0);
}

//@pbe (constraint (= (f499f "404" 3 3) 1))
//@pbe (constraint (= (f499f "ab cd" 3 6) 1))
//@pbe (constraint (= (f499f "mno pqr st" 4 7) 2))