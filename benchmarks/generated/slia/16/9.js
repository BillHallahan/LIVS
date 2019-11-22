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

function f184f(x_0, x_1)
{
	return mult(len(x_1), len(x_0));
}

function f399f(x_0, x_1, x_2)
{
	return toStr(add(x_2, x_2));
}

function f115f(x_0, x_1, x_2)
{
	return len(concat(x_2, x_0));
}

function f487f(x_0)
{
	return f184f(concat(x_0, x_0), beforeAfter(x_0));
}

function f381f(x_0, x_1)
{
	return len(toStr(x_0));
}

function f842f(x_0, x_1, x_2)
{
	return f399f(concat(x_0, x_0), concat(x_2, x_0), add(x_1, x_1));
}

function f949f(x_0, x_1, x_2)
{
	return f184f(beforeAfter(x_1), f842f(x_1, x_2, x_1));
}

function f146f(x_0, x_1)
{
	return mult(f115f(x_1, x_1, x_1), f949f(x_1, x_1, x_0));
}

function f626f(x_0, x_1)
{
	return f487f(x_0);
}

//@pbe (constraint (= (f171f "asdf") 320))
//@pbe (constraint (= (f171f "vvvvv") 720))
//@pbe (constraint (= (f171f "mno pqr st") 2640))
//@pbe (constraint (= (f171f "asdf") 320))
//@pbe (constraint (= (f171f "404") 192))