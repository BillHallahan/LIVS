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

function f260f(x_0, x_1, x_2)
{
	return mult(f565f(x_2, x_0, x_0), f565f(x_1, x_0, x_0));
}

function f637f(x_0, x_1)
{
	return toStr(x_1);
}

function f50f(x_0, x_1, x_2)
{
	return toStr(f565f(x_0, x_2, x_2));
}

//@pbe (constraint (= (f242f 2 "hello world" "vvvvv") 20))
//@pbe (constraint (= (f242f -3 "xyz" "ab cd") 30))
//@pbe (constraint (= (f242f 5 "hello world" "asdf") 110))