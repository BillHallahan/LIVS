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

function f750f(x_0, x_1)
{
	return firstWord(x_1);
}

function f189f(x_0, x_1, x_2)
{
	return beforeAfter(len(x_1));
}

function f973f(x_0, x_1)
{
	return rep(f750f(x_1, x_1), len(x_1), concat(x_0, x_1));
}

function f720f(x_0, x_1, x_2)
{
	return f189f(f973f(x_2, x_2), x_2, concat(x_2, x_0));
}

function f308f(x_0)
{
	return firstWord(beforeAfter(x_0));
}

function f408f(x_0, x_1)
{
	return concat(rep(x_0, x_1, x_1), rep(x_0, x_0, x_0));
}

function f896f(x_0, x_1)
{
	return f720f(beforeAfter(x_1), lastLetter(x_0), beforeAfter(x_0));
}

function f618f(x_0)
{
	return f408f(f720f(x_0, x_0, x_0), concat(x_0, x_0));
}

function f644f(x_0, x_1, x_2)
{
	return concat(f189f(x_1, x_1, x_0), beforeAfter(x_1));
}

//@pbe (constraint (= (f604f "mno pqr st") "1010"))
//@pbe (constraint (= (f604f "ab cd") "55"))