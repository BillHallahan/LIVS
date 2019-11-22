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

function f964f(x_0, x_1, x_2)
{
	return firstWord(concat(x_2, x_2));
}

function f82f(x_0, x_1, x_2)
{
	return concat(firstWord(x_0), rep(x_0, x_2, x_1));
}

function f74f(x_0, x_1)
{
	return concat(concat(x_0, x_1), f48f(x_1, x_0, x_0));
}

function f948f(x_0)
{
	return rep(f48f(x_0, x_0, x_0), rep(x_0, x_0, x_0), x_0);
}

function f296f(x_0)
{
	return lastLetter(f948f(x_0));
}

function f838f(x_0, x_1, x_2)
{
	return f48f(x_0, f296f(x_0), x_1);
}

//@pbe (constraint (= (f94f "404" "mno pqr st") "4B404A4"))
//@pbe (constraint (= (f94f "xyz" "xyz") "zBxyzAz"))
//@pbe (constraint (= (f94f "ab cd" "404") "dBab cdAd"))