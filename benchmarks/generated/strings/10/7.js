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

function f232f(x_0)
{
	return beforeAfter(concat(x_0, x_0));
}

function f481f(x_0, x_1, x_2)
{
	return beforeAfter(firstWord(x_0));
}

function f111f(x_0, x_1, x_2)
{
	return f481f(x_1, firstWord(x_2), firstWord(x_0));
}

function f338f(x_0)
{
	return len(beforeAfter(x_0));
}

function f920f(x_0)
{
	return concat(rep(x_0, x_0, x_0), lastLetter(x_0));
}

function f700f(x_0)
{
	return f338f(f481f(x_0, x_0, x_0));
}

function f320f(x_0, x_1)
{
	return f700f(x_1);
}

//@pbe (constraint (= (f425f "hello world") "hello"))
//@pbe (constraint (= (f425f "vvvvv") ""))
//@pbe (constraint (= (f425f "mno pqr st") "mno"))
//@pbe (constraint (= (f425f "mno pqr st") "mno"))
//@pbe (constraint (= (f425f "ab cd") "ab"))