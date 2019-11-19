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

function f391f(x_0, x_1, x_2)
{
	return rep(rep(x_2, x_0, x_2), x_0, beforeAfter(x_0));
}

function f0f(x_0, x_1, x_2)
{
	return beforeAfter(beforeAfter(x_2));
}

//@pbe (constraint (= (f94f "mno pqr st" "vvvvv" "asdf") "Bmno pqr stA"))
//@pbe (constraint (= (f94f "404" "hello world" "mno pqr st") "B404A"))
//@pbe (constraint (= (f94f "hello world" "vvvvv" "vvvvv") "Bhello worldA"))
//@pbe (constraint (= (f94f "" "" "404") "BBAA"))