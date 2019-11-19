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

//@pbe (constraint (= (f416f "" "mno pqr st" "mno pqr st") "BBmno pqr stAA"))
//@pbe (constraint (= (f416f "hello world" "mno pqr st" "asdf") "BBasdfAA"))
//@pbe (constraint (= (f416f "hello world" "hello world" "vvvvv") "BBvvvvvAA"))
//@pbe (constraint (= (f416f "404" "hello world" "404") "BB404AA"))