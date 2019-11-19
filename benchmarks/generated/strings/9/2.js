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

//@pbe (constraint (= (f959f "404" "ab cd") "Bab cdA5"))
//@pbe (constraint (= (f959f "vvvvv" "mno pqr st") "Bmno pqr stA10"))
//@pbe (constraint (= (f959f "404" "mno pqr st") "Bmno pqr stA10"))
//@pbe (constraint (= (f959f "vvvvv" "asdf") "BasdfA4"))
//@pbe (constraint (= (f959f "asdf" "404") "B404A3"))