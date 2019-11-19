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

function f482f(x_0)
{
	return beforeAfter(beforeAfter(x_0));
}

function f238f(x_0, x_1, x_2)
{
	return beforeAfter(x_1);
}

function f866f(x_0, x_1, x_2)
{
	return f238f(x_0, concat(x_2, x_2), concat(x_2, x_2));
}

function f693f(x_0, x_1)
{
	return len(concat(x_1, x_1));
}

function f294f(x_0, x_1, x_2)
{
	return f238f(f693f(x_2, x_0), toStr(x_1), beforeAfter(x_0));
}

//@pbe (constraint (= (f488f "vvvvv" 10 "xyz") "B110A"))
//@pbe (constraint (= (f488f "404" 0 "404") "B10A"))
//@pbe (constraint (= (f488f "hello world" 10 "hello world") "B110A"))
//@pbe (constraint (= (f488f "ab cd" 6 "mno pqr st") "B46A"))
//@pbe (constraint (= (f488f "xyz" 8 "mno pqr st") "B74A"))