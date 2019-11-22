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

//@pbe (constraint (= (f82f "ab cd" "mno pqr st" "ab cd") "abmno pqr st"))
//@pbe (constraint (= (f82f "ab cd" "vvvvv" "hello world") "abab cd"))
//@pbe (constraint (= (f82f "mno pqr st" "hello world" "404") "mnomno pqr st"))