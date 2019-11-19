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

function f478f(x_0, x_1, x_2)
{
	return beforeAfter(concat(x_1, x_1));
}

function f559f(x_0, x_1, x_2)
{
	return toStr(add(x_1, x_1));
}

function f424f(x_0)
{
	return add(add(x_0, x_0), x_0);
}

function f605f(x_0, x_1)
{
	return len(x_0);
}

//@pbe (constraint (= (f62f "" "404" 1) 9))
//@pbe (constraint (= (f62f "xyz" "" 6) 54))
//@pbe (constraint (= (f62f "asdf" "xyz" -5) -45))