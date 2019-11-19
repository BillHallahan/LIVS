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

function f371f(x_0)
{
	return rep(firstWord(x_0), concat(x_0, x_0), f876f(x_0));
}

//@pbe (constraint (= (f619f "ab cd") "10"))
//@pbe (constraint (= (f619f "xyz") "6"))
//@pbe (constraint (= (f619f "asdf") "8"))