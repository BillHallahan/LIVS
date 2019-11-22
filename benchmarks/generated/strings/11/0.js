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

//@pbe (constraint (= (f365f "ab cd" "404") "B404A5"))
//@pbe (constraint (= (f365f "ab cd" "mno pqr st") "Bmno pqr stA5"))
//@pbe (constraint (= (f365f "asdf" "asdf") "BasdfA4"))
//@pbe (constraint (= (f365f "ab cd" "xyz") "BxyzA5"))
//@pbe (constraint (= (f365f "ab cd" "mno pqr st") "Bmno pqr stA5"))