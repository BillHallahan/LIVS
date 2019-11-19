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

function f432f(x_0, x_1, x_2)
{
	return f45f(x_1, f604f(x_1, x_2), lastLetter(x_0));
}

function f651f(x_0)
{
	return firstWord(f45f(x_0, x_0, x_0));
}

function f797f(x_0)
{
	return f45f(firstWord(x_0), lastLetter(x_0), beforeAfter(x_0));
}

function f208f(x_0, x_1)
{
	return firstWord(beforeAfter(x_0));
}

function f472f(x_0)
{
	return f208f(concat(x_0, x_0), firstWord(x_0));
}

function f917f(x_0, x_1)
{
	return rep(f208f(x_1, x_1), f208f(x_0, x_0), concat(x_1, x_1));
}

function f170f(x_0, x_1, x_2)
{
	return concat(firstWord(x_0), x_1);
}

//@pbe (constraint (= (f569f "hello world" "hello world" "hello world") "d"))
//@pbe (constraint (= (f569f "xyz" "mno pqr st" "mno pqr st") "z"))