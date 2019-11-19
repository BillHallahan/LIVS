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

function f281f(x_0, x_1, x_2)
{
	return rep(beforeAfter(x_1), x_2, rep(x_1, x_0, x_0));
}

function f979f(x_0, x_1, x_2)
{
	return lastLetter(firstWord(x_2));
}

function f256f(x_0, x_1, x_2)
{
	return concat(concat(x_0, x_2), len(x_1));
}

function f418f(x_0, x_1)
{
	return rep(x_1, f281f(x_1, x_0, x_1), beforeAfter(x_0));
}

function f515f(x_0)
{
	return concat(len(x_0), x_0);
}

function f250f(x_0, x_1)
{
	return beforeAfter(rep(x_0, x_1, x_0));
}

//@pbe (constraint (= (f338f "ab cd") "BBBab cdAAA"))
//@pbe (constraint (= (f338f "ab cd") "BBBab cdAAA"))
//@pbe (constraint (= (f338f "ab cd") "BBBab cdAAA"))
//@pbe (constraint (= (f338f "ab cd") "BBBab cdAAA"))