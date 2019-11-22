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

function f212f(x_0, x_1)
{
	return concat(beforeAfter(x_0), len(x_1));
}

function f432f(x_0, x_1)
{
	return len(f212f(x_1, x_0));
}

function f177f(x_0, x_1, x_2)
{
	return f432f(rep(x_0, x_2, x_1), rep(x_1, x_0, x_0));
}

//@pbe (constraint (= (f133f "asdf" "mno pqr st" "ab cd") "7"))
//@pbe (constraint (= (f133f "xyz" "mno pqr st" "404") "6"))
//@pbe (constraint (= (f133f "mno pqr st" "404" "asdf") "13"))