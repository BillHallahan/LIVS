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

function f581f(x_0, x_1)
{
	return firstWord(concat(x_1, x_0));
}

function f444f(x_0, x_1)
{
	return lastLetter(f581f(x_0, x_0));
}

function f219f(x_0, x_1, x_2)
{
	return rep(f444f(x_1, x_2), x_0, len(x_2));
}

//@pbe (constraint (= (f925f "") "00"))
//@pbe (constraint (= (f925f "xyz") ""))