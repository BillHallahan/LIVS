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

function f214f(x_0)
{
	return beforeAfter(rep(x_0, x_0, x_0));
}

function f634f(x_0, x_1, x_2)
{
	return concat(firstWord(x_0), lastLetter(x_1));
}

function f502f(x_0, x_1, x_2)
{
	return rep(firstWord(x_0), beforeAfter(x_2), firstWord(x_0));
}

function f324f(x_0, x_1)
{
	return concat(lastLetter(x_1), f502f(x_1, x_0, x_1));
}

function f262f(x_0, x_1)
{
	return f324f(f502f(x_1, x_1, x_0), len(x_0));
}

function f359f(x_0)
{
	return lastLetter(rep(x_0, x_0, x_0));
}

function f67f(x_0, x_1)
{
	return concat(concat(x_0, x_0), f502f(x_0, x_0, x_1));
}

//@pbe (constraint (= (f415f "mno pqr st") "Bmno"))
//@pbe (constraint (= (f415f "xyz") ""))
//@pbe (constraint (= (f415f "mno pqr st") "Bmno"))
//@pbe (constraint (= (f415f "xyz") ""))
//@pbe (constraint (= (f415f "vvvvv") ""))