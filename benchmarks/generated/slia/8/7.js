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

function f783f(x_0, x_1, x_2)
{
	return toStr(add(x_2, x_2));
}

function f34f(x_0, x_1, x_2)
{
	return concat(f783f(x_0, x_0, x_2), toStr(x_2));
}

function f937f(x_0)
{
	return mult(x_0, mult(x_0, x_0));
}

function f836f(x_0, x_1, x_2)
{
	return mult(x_2, len(x_1));
}

function f425f(x_0, x_1)
{
	return toStr(add(x_1, x_1));
}

function f147f(x_0, x_1, x_2)
{
	return f425f(beforeAfter(x_0), len(x_2));
}

function f254f(x_0, x_1)
{
	return mult(f836f(x_1, x_1, x_0), f937f(x_0));
}

//@pbe (constraint (= (f789f -4 "vvvvv" "xyz") 27))
//@pbe (constraint (= (f789f 9 "xyz" "mno pqr st") 1000))
//@pbe (constraint (= (f789f 7 "" "mno pqr st") 1000))
//@pbe (constraint (= (f789f 1 "ab cd" "xyz") 27))