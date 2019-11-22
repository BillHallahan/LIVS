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

function f64f(x_0, x_1, x_2)
{
	return beforeAfter(x_2);
}

function f785f(x_0, x_1, x_2)
{
	return rep(beforeAfter(x_1), len(x_1), firstWord(x_1));
}

function f855f(x_0, x_1, x_2)
{
	return beforeAfter(x_0);
}

function f778f(x_0)
{
	return firstWord(x_0);
}

//@pbe (constraint (= (f455f "vvvvv" "xyz") "BvA"))
//@pbe (constraint (= (f455f "xyz" "vvvvv") "BzA"))