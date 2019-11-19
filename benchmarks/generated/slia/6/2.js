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

//@pbe (constraint (= (f858f "ab cd" "") 20))
//@pbe (constraint (= (f858f "" "hello world") 0))
//@pbe (constraint (= (f858f "asdf" "ab cd") 16))
//@pbe (constraint (= (f858f "404" "ab cd") 12))