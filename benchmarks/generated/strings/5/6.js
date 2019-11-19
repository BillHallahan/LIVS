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

function f397f(x_0, x_1, x_2)
{
	return concat(x_2, lastLetter(x_1));
}

function f665f(x_0, x_1)
{
	return rep(len(x_0), concat(x_1, x_1), len(x_1));
}

function f123f(x_0, x_1, x_2)
{
	return beforeAfter(x_1);
}

function f156f(x_0, x_1, x_2)
{
	return concat(firstWord(x_1), beforeAfter(x_2));
}

function f708f(x_0)
{
	return lastLetter(f397f(x_0, x_0, x_0));
}

function f716f(x_0)
{
	return f156f(f665f(x_0, x_0), beforeAfter(x_0), x_0);
}

//@pbe (constraint (= (f918f "ab cd") "ab cdd"))
//@pbe (constraint (= (f918f "mno pqr st") "mno pqr stt"))
//@pbe (constraint (= (f918f "404") "4044"))