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

//@pbe (constraint (= (f212f "xyz" "vvvvv") "BxyzA5"))
//@pbe (constraint (= (f212f "vvvvv" "404") "BvvvvvA3"))
//@pbe (constraint (= (f212f "mno pqr st" "xyz") "Bmno pqr stA3"))
//@pbe (constraint (= (f212f "404" "asdf") "B404A4"))
//@pbe (constraint (= (f212f "404" "xyz") "B404A3"))