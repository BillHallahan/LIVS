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

function f710f(x_0)
{
	return len(lastLetter(x_0));
}

function f390f(x_0, x_1)
{
	return rep(x_1, len(x_0), concat(x_1, x_1));
}

function f353f(x_0, x_1)
{
	return beforeAfter(rep(x_0, x_1, x_1));
}

//@pbe (constraint (= (f193f "404" "xyz") "404"))
//@pbe (constraint (= (f193f "404" "404") "404"))