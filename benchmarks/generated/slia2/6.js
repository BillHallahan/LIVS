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

function increment(x_0)
{
	return x_0 + 1;
}

function len(x_0)
{
	return x_0.length;
}

function toStr(x_0)
{
	return x_0 + "";
}

function appendNum(x_0, x_1)
{
	return x_1 + x_0;
}

function rptStr(x_0, x_1)
{
	if(x_1 <= 5) { return x_0.repeat(x_1); } else { return x_0.repeat(5); }
}

function f69f(x_0, x_1)
{
	return mult(x_1, x_0);
}

function f41f(x_0, x_1)
{
	return mult(mult(x_0, x_0), add(x_0, x_0));
}

function f50f(x_0, x_1, x_2)
{
	return rptStr(rptStr(x_0, x_2), increment(x_2));
}

function f10f(x_0, x_1, x_2)
{
	return add(len(x_0), f41f(x_1, x_0));
}

function f16f(x_0, x_1, x_2)
{
	return toStr(f69f(x_1, x_1));
}

function f21f(x_0, x_1)
{
	return f10f(x_1, len(x_0), len(x_0));
}

//@pbe (constraint (= (f65f "hi" 7) 52))
//@pbe (constraint (= (f65f "404" 8) 77))
//@pbe (constraint (= (f65f "hi" 4) 42))
//@pbe (constraint (= (f65f "" 3) 2))
//@pbe (constraint (= (f65f "404" 8) 77))