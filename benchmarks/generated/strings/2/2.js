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

function f490f(x_0, x_1)
{
	return concat(x_1, x_1);
}

function f876f(x_0)
{
	return firstWord(beforeAfter(x_0));
}

//@pbe (constraint (= (f371f "404") ""))
//@pbe (constraint (= (f371f "") ""))
//@pbe (constraint (= (f371f "ab cd") "ab"))
//@pbe (constraint (= (f371f "mno pqr st") "mno"))
//@pbe (constraint (= (f371f "ab cd") "ab"))