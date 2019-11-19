function add(x_0, x_1)
{
	return x_0 + x_1;
}

function mult(x_0, x_1)
{
	return x_0 * x_1;
}

function increment(x_0)
{
	return x_0 + 1;
}

function decrement(x_0)
{
	return x_0 - 1;
}

function subtract(x_0, x_1)
{
	return x_0 - x_1;
}

function double(x_0)
{
	return x_0 * 2;
}

function f370f(x_0, x_1, x_2)
{
	return increment(double(x_2));
}

function f449f(x_0, x_1, x_2)
{
	return mult(decrement(x_1), mult(x_2, x_2));
}

function f323f(x_0, x_1)
{
	return double(double(x_0));
}

function f978f(x_0, x_1)
{
	return double(f449f(x_0, x_0, x_0));
}

function f841f(x_0)
{
	return f449f(x_0, f370f(x_0, x_0, x_0), f978f(x_0, x_0));
}

function f261f(x_0, x_1, x_2)
{
	return add(x_2, increment(x_0));
}

function f745f(x_0)
{
	return f841f(f978f(x_0, x_0));
}

//@pbe (constraint (= (f6f -3) -66347631739817165000))
//@pbe (constraint (= (f6f 9) 1.5746303799950339e+29))
//@pbe (constraint (= (f6f 8) 1.260391374249258e+28))
//@pbe (constraint (= (f6f -2) -21744110796800000))
//@pbe (constraint (= (f6f -3) -66347631739817165000))