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

function f604f(x_0, x_1)
{
	return firstWord(x_1);
}

function f45f(x_0, x_1, x_2)
{
	return rep(x_1, beforeAfter(x_2), firstWord(x_1));
}

//@pbe (constraint (= (f432f "asdf" "vvvvv" "ab cd") "ab"))
//@pbe (constraint (= (f432f "asdf" "xyz" "mno pqr st") "mno"))
//@pbe (constraint (= (f432f "asdf" "ab cd" "asdf") ""))
//@pbe (constraint (= (f432f "asdf" "xyz" "xyz") ""))
//@pbe (constraint (= (f432f "mno pqr st" "xyz" "ab cd") "ab"))