function concat(x_0, x_1)
{
	return x_0 + x_1;
}

function len(x_0)
{
	return x_0.length + "";
}

function beforeAfter(x_0)
{
	return 'B' + x_0 + 'A';
}

function lastLetter(x_0)
{
	if (x_0.length > 0) { return x_0.slice(-1); } else { return ''; }
}

function firstWord(x_0)
{
	return x_0.substring(0, x_0.indexOf(" "));
}

function rep(x_0, x_1, x_2)
{
	return x_0.replace(x_1, x_2);
}

function f342f(x_0, x_1, x_2)
{
	return len(x_1);
}

function f304f(x_0)
{
	return f342f(rep(x_0, x_0, x_0), beforeAfter(x_0), len(x_0));
}

function f802f(x_0)
{
	return lastLetter(x_0);
}

function f424f(x_0, x_1)
{
	return beforeAfter(len(x_0));
}

function f775f(x_0, x_1)
{
	return f424f(len(x_0), f342f(x_1, x_0, x_0));
}

function f765f(x_0)
{
	return beforeAfter(beforeAfter(x_0));
}

function f275f(x_0, x_1)
{
	return f304f(f765f(x_0));
}

//@pbe (constraint (= (f789f "ab cd" "xyz") "d"))
//@pbe (constraint (= (f789f "ab cd" "vvvvv") "d"))
//@pbe (constraint (= (f789f "hello world" "xyz") "d"))
//@pbe (constraint (= (f789f "asdf" "hello world") "f"))
//@pbe (constraint (= (f789f "xyz" "hello world") "z"))