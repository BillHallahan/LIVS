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

function f394f(x_0)
{
	return concat(firstWord(x_0), x_0);
}

function f48f(x_0, x_1, x_2)
{
	return f394f(x_2);
}

//@pbe (constraint (= (f964f "404" "hello world" "ab cd") "ab"))
//@pbe (constraint (= (f964f "xyz" "404" "asdf") ""))
//@pbe (constraint (= (f964f "hello world" "asdf" "mno pqr st") "mno"))
//@pbe (constraint (= (f964f "vvvvv" "asdf" "asdf") ""))
//@pbe (constraint (= (f964f "ab cd" "404" "hello world") "hello"))