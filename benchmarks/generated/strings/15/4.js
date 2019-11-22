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

function f383f(x_0, x_1)
{
	return beforeAfter(lastLetter(x_1));
}

function f1000f(x_0, x_1, x_2)
{
	return concat(x_2, lastLetter(x_1));
}

function f984f(x_0)
{
	return f1000f(concat(x_0, x_0), rep(x_0, x_0, x_0), f1000f(x_0, x_0, x_0));
}

function f237f(x_0, x_1)
{
	return beforeAfter(f1000f(x_1, x_0, x_0));
}

//@pbe (constraint (= (f354f "mno pqr st") "Bmno pqr stmno pqr sttA"))
//@pbe (constraint (= (f354f "xyz") "BxyzxyzzA"))
//@pbe (constraint (= (f354f "404") "B4044044A"))