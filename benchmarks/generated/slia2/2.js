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

//@pbe (constraint (= (f50f "asdf" 6 6) "asdfasdfasdfasdfasdfasdfasdfasdfasdfasdfasdfasdfasdfasdfasdfasdfasdfasdfasdfasdfasdfasdfasdfasdfasdf"))
//@pbe (constraint (= (f50f "" 6 1) ""))
//@pbe (constraint (= (f50f "" 0 3) ""))
//@pbe (constraint (= (f50f "404" 1 7) "404404404404404404404404404404404404404404404404404404404404404404404404404"))
//@pbe (constraint (= (f50f "asdf" 4 6) "asdfasdfasdfasdfasdfasdfasdfasdfasdfasdfasdfasdfasdfasdfasdfasdfasdfasdfasdfasdfasdfasdfasdfasdfasdf"))