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

function f923f(x_0, x_1, x_2)
{
	return firstWord(x_0);
}

function f826f(x_0)
{
	return beforeAfter(beforeAfter(x_0));
}

function f951f(x_0, x_1, x_2)
{
	return concat(x_0, firstWord(x_2));
}

//@pbe (constraint (= (f454f "mno pqr st" "hello world" "mno pqr st") "mno"))
//@pbe (constraint (= (f454f "asdf" "xyz" "404") ""))
//@pbe (constraint (= (f454f "asdf" "404" "hello world") ""))
//@pbe (constraint (= (f454f "ab cd" "ab cd" "ab cd") "ab"))
//@pbe (constraint (= (f454f "asdf" "asdf" "mno pqr st") ""))