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

function f183f(x_0)
{
	return beforeAfter(beforeAfter(x_0));
}

function f759f(x_0, x_1)
{
	return f183f(x_0);
}

function f565f(x_0, x_1, x_2)
{
	return add(x_2, x_2);
}

function f684f(x_0, x_1, x_2)
{
	return concat(x_0, x_1);
}

function f835f(x_0, x_1, x_2)
{
	return beforeAfter(f183f(x_1));
}

//@pbe (constraint (= (f260f -5 "404" "ab cd") 100))
//@pbe (constraint (= (f260f 3 "vvvvv" "asdf") 36))
//@pbe (constraint (= (f260f 4 "hello world" "vvvvv") 64))