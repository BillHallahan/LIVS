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

function f163f(x_0, x_1)
{
	return firstWord(rep(x_0, x_1, x_0));
}

function f60f(x_0)
{
	return rep(x_0, beforeAfter(x_0), concat(x_0, x_0));
}

function f412f(x_0, x_1)
{
	return firstWord(f60f(x_1));
}

function f621f(x_0, x_1, x_2)
{
	return firstWord(concat(x_0, x_1));
}

//@pbe (constraint (= (f746f "vvvvv" "asdf" "mno pqr st") "mno pqr st"))
//@pbe (constraint (= (f746f "404" "asdf" "xyz") "xyz"))