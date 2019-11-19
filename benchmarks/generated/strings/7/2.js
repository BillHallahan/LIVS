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

function f350f(x_0)
{
	return concat(x_0, concat(x_0, x_0));
}

function f967f(x_0, x_1)
{
	return concat(f350f(x_1), len(x_1));
}

//@pbe (constraint (= (f611f "404" "404" "ab cd") "15"))
//@pbe (constraint (= (f611f "mno pqr st" "" "") "0"))
//@pbe (constraint (= (f611f "asdf" "mno pqr st" "asdf") "12"))
//@pbe (constraint (= (f611f "asdf" "asdf" "xyz") "9"))