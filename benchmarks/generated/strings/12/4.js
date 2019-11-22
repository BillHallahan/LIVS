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

function f102f(x_0, x_1, x_2)
{
	return len(x_0);
}

function f605f(x_0, x_1, x_2)
{
	return beforeAfter(rep(x_2, x_2, x_2));
}

function f244f(x_0, x_1, x_2)
{
	return f605f(lastLetter(x_0), rep(x_1, x_2, x_0), firstWord(x_2));
}

function f253f(x_0, x_1, x_2)
{
	return concat(x_0, firstWord(x_1));
}

//@pbe (constraint (= (f127f "asdf") "BA"))
//@pbe (constraint (= (f127f "xyz") "BA"))
//@pbe (constraint (= (f127f "404") "BA"))
//@pbe (constraint (= (f127f "xyz") "BA"))