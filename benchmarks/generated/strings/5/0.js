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

//@pbe (constraint (= (f397f "mno pqr st" "xyz" "vvvvv") "vvvvvz"))
//@pbe (constraint (= (f397f "vvvvv" "asdf" "vvvvv") "vvvvvf"))
//@pbe (constraint (= (f397f "" "" "asdf") "asdf"))