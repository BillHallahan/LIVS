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

function f190f(x_0, x_1)
{
	return len(rep(x_1, x_1, x_0));
}

function f871f(x_0, x_1, x_2)
{
	return len(len(x_1));
}

function f832f(x_0, x_1)
{
	return f190f(firstWord(x_1), beforeAfter(x_0));
}

//@pbe (constraint (= (f943f "mno pqr st") "3"))
//@pbe (constraint (= (f943f "") "0"))
//@pbe (constraint (= (f943f "mno pqr st") "3"))