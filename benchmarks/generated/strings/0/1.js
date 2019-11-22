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

function f0f(x_0)
{
	return concat(len(x_0), firstWord(x_0));
}

//@pbe (constraint (= (f352f "vvvvv" "mno pqr st") "5"))
//@pbe (constraint (= (f352f "mno pqr st" "404") "10mno"))
//@pbe (constraint (= (f352f "vvvvv" "hello world") "5"))
//@pbe (constraint (= (f352f "asdf" "ab cd") "4"))