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

function f454f(x_0, x_1, x_2)
{
	return len(concat(x_2, x_2));
}

function f537f(x_0, x_1, x_2)
{
	return f454f(len(x_1), x_0, beforeAfter(x_1));
}

function f858f(x_0, x_1)
{
	return f454f(len(x_1), concat(x_0, x_1), concat(x_0, x_0));
}

function f348f(x_0)
{
	return f858f(toStr(x_0), toStr(x_0));
}

function f155f(x_0, x_1)
{
	return beforeAfter(toStr(x_0));
}

function f758f(x_0, x_1)
{
	return f155f(f454f(x_0, x_1, x_1), f348f(x_0));
}

function f467f(x_0, x_1, x_2)
{
	return mult(f537f(x_0, x_0, x_2), f537f(x_1, x_0, x_2));
}

function f636f(x_0, x_1)
{
	return toStr(mult(x_1, x_1));
}

//@pbe (constraint (= (f518f "404" 10) "404404B16A"))
//@pbe (constraint (= (f518f "" 7) "B10A"))
//@pbe (constraint (= (f518f "mno pqr st" 3) "mno pqr stmno pqr stB30A"))
//@pbe (constraint (= (f518f "404" 1) "404404B16A"))
//@pbe (constraint (= (f518f "xyz" 9) "xyzxyzB16A"))