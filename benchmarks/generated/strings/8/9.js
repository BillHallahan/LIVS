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

function f116f(x_0, x_1)
{
	return lastLetter(concat(x_1, x_0));
}

function f473f(x_0, x_1, x_2)
{
	return beforeAfter(x_2);
}

function f820f(x_0, x_1)
{
	return len(firstWord(x_1));
}

function f745f(x_0)
{
	return f116f(f116f(x_0, x_0), lastLetter(x_0));
}

function f695f(x_0)
{
	return rep(f473f(x_0, x_0, x_0), beforeAfter(x_0), rep(x_0, x_0, x_0));
}

function f545f(x_0, x_1, x_2)
{
	return f820f(f745f(x_0), rep(x_2, x_2, x_1));
}

function f33f(x_0)
{
	return f473f(f545f(x_0, x_0, x_0), f545f(x_0, x_0, x_0), firstWord(x_0));
}

function f469f(x_0, x_1)
{
	return len(f695f(x_0));
}

function f344f(x_0, x_1)
{
	return f545f(concat(x_1, x_0), x_1, firstWord(x_0));
}

//@pbe (constraint (= (f997f "ab cd" "hello world" "asdf") "11"))
//@pbe (constraint (= (f997f "hello world" "hello world" "asdf") "11"))