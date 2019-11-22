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

function f212f(x_0, x_1)
{
	return concat(beforeAfter(x_0), len(x_1));
}

function f432f(x_0, x_1)
{
	return len(f212f(x_1, x_0));
}

function f177f(x_0, x_1, x_2)
{
	return f432f(rep(x_0, x_2, x_1), rep(x_1, x_0, x_0));
}

function f133f(x_0, x_1, x_2)
{
	return f432f(f177f(x_1, x_0, x_1), x_0);
}

function f396f(x_0)
{
	return f177f(beforeAfter(x_0), f177f(x_0, x_0, x_0), len(x_0));
}

function f403f(x_0)
{
	return len(firstWord(x_0));
}

function f361f(x_0, x_1)
{
	return f133f(f212f(x_0, x_0), len(x_1), f212f(x_0, x_0));
}

//@pbe (constraint (= (f533f "vvvvv") "8"))
//@pbe (constraint (= (f533f "404") "6"))
//@pbe (constraint (= (f533f "xyz") "6"))