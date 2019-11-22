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

//@pbe (constraint (= (f399f "404" "xyz" 5) "10"))
//@pbe (constraint (= (f399f "hello world" "ab cd" 0) "0"))
//@pbe (constraint (= (f399f "hello world" "mno pqr st" 10) "20"))
//@pbe (constraint (= (f399f "vvvvv" "ab cd" 10) "20"))
//@pbe (constraint (= (f399f "xyz" "404" 4) "8"))