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

function f741f(x_0, x_1, x_2)
{
	return lastLetter(len(x_1));
}

function f933f(x_0, x_1, x_2)
{
	return f741f(len(x_1), x_0, firstWord(x_2));
}

function f449f(x_0, x_1)
{
	return concat(f741f(x_1, x_1, x_1), f741f(x_1, x_1, x_1));
}

function f930f(x_0)
{
	return f741f(f449f(x_0, x_0), concat(x_0, x_0), beforeAfter(x_0));
}

function f793f(x_0)
{
	return beforeAfter(lastLetter(x_0));
}

//@pbe (constraint (= (f959f "hello world" "ab cd") "0"))
//@pbe (constraint (= (f959f "mno pqr st" "404") "6"))