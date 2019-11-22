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

function f696f(x_0)
{
	return mult(mult(x_0, x_0), x_0);
}

function f405f(x_0, x_1, x_2)
{
	return len(concat(x_2, x_0));
}

function f213f(x_0)
{
	return concat(beforeAfter(x_0), x_0);
}

//@pbe (constraint (= (f684f "404" 0 "vvvvv") "404B404A"))
//@pbe (constraint (= (f684f "xyz" 4 "ab cd") "xyzBxyzA"))
//@pbe (constraint (= (f684f "404" 10 "404") "404B404A"))
//@pbe (constraint (= (f684f "asdf" 5 "asdf") "asdfBasdfA"))
//@pbe (constraint (= (f684f "ab cd" 5 "vvvvv") "ab cdBab cdA"))