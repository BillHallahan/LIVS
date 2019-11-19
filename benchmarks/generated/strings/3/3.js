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

function f675f(x_0, x_1)
{
	return beforeAfter(len(x_1));
}

function f380f(x_0, x_1)
{
	return len(firstWord(x_0));
}

function f230f(x_0, x_1, x_2)
{
	return rep(f675f(x_0, x_0), concat(x_0, x_2), concat(x_0, x_1));
}

//@pbe (constraint (= (f560f "mno pqr st" "404" "asdf") "B0A"))
//@pbe (constraint (= (f560f "" "mno pqr st" "mno pqr st") "B3A"))
//@pbe (constraint (= (f560f "xyz" "hello world" "hello world") "B5A"))