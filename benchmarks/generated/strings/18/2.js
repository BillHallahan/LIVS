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

function f411f(x_0, x_1, x_2)
{
	return firstWord(rep(x_1, x_2, x_0));
}

function f718f(x_0, x_1, x_2)
{
	return f411f(beforeAfter(x_1), rep(x_0, x_1, x_2), x_2);
}

//@pbe (constraint (= (f608f "ab cd") "BabA"))
//@pbe (constraint (= (f608f "mno pqr st") "BmnoA"))