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

function f209f(x_0)
{
	return firstWord(beforeAfter(x_0));
}

function f416f(x_0, x_1, x_2)
{
	return beforeAfter(beforeAfter(x_2));
}

function f959f(x_0, x_1)
{
	return concat(beforeAfter(x_1), len(x_1));
}

function f386f(x_0, x_1)
{
	return rep(rep(x_1, x_0, x_1), beforeAfter(x_0), firstWord(x_1));
}

function f12f(x_0, x_1)
{
	return f416f(x_0, f416f(x_1, x_0, x_0), concat(x_1, x_0));
}

//@pbe (constraint (= (f91f "404" "xyz" "xyz") "BBBxyzAxyzAA"))
//@pbe (constraint (= (f91f "" "xyz" "xyz") "BBBxyzAxyzAA"))
//@pbe (constraint (= (f91f "xyz" "hello world" "xyz") "BBBhello worldAhello worldAA"))