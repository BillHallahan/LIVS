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

function f135f(x_0, x_1, x_2)
{
	return len(x_0);
}

function f569f(x_0)
{
	return toStr(f135f(x_0, x_0, x_0));
}

function f455f(x_0, x_1, x_2)
{
	return f569f(x_0);
}

function f560f(x_0, x_1, x_2)
{
	return add(x_2, x_2);
}

//@pbe (constraint (= (f66f 6 "ab cd" "hello world") "22"))
//@pbe (constraint (= (f66f 5 "hello world" "vvvvv") "10"))
//@pbe (constraint (= (f66f 0 "mno pqr st" "404") "6"))
//@pbe (constraint (= (f66f 7 "asdf" "mno pqr st") "20"))
//@pbe (constraint (= (f66f 5 "ab cd" "ab cd") "10"))