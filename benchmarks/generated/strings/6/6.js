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

function f391f(x_0, x_1, x_2)
{
	return rep(rep(x_2, x_0, x_2), x_0, beforeAfter(x_0));
}

function f0f(x_0, x_1, x_2)
{
	return beforeAfter(beforeAfter(x_2));
}

function f94f(x_0, x_1, x_2)
{
	return beforeAfter(f391f(x_1, x_0, x_0));
}

function f992f(x_0, x_1)
{
	return len(firstWord(x_1));
}

function f264f(x_0, x_1)
{
	return f94f(x_0, lastLetter(x_1), f94f(x_1, x_0, x_1));
}

function f986f(x_0)
{
	return len(f264f(x_0, x_0));
}

//@pbe (constraint (= (f196f "vvvvv" "xyz") "BA"))
//@pbe (constraint (= (f196f "ab cd" "xyz") "BabA"))
//@pbe (constraint (= (f196f "xyz" "asdf") "BA"))
//@pbe (constraint (= (f196f "404" "ab cd") "BA"))
//@pbe (constraint (= (f196f "ab cd" "hello world") "BabA"))