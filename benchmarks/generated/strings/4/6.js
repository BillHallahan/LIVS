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

function f54f(x_0, x_1, x_2)
{
	return len(rep(x_2, x_2, x_0));
}

function f833f(x_0)
{
	return beforeAfter(rep(x_0, x_0, x_0));
}

function f357f(x_0, x_1)
{
	return f54f(x_1, x_1, f54f(x_1, x_1, x_1));
}

function f210f(x_0)
{
	return rep(x_0, len(x_0), f357f(x_0, x_0));
}

function f617f(x_0, x_1)
{
	return f833f(f357f(x_1, x_1));
}

function f650f(x_0)
{
	return concat(len(x_0), f617f(x_0, x_0));
}

//@pbe (constraint (= (f764f "404" "mno pqr st" "ab cd") "B7A"))
//@pbe (constraint (= (f764f "mno pqr st" "404" "vvvvv") "B7A"))
//@pbe (constraint (= (f764f "vvvvv" "hello world" "ab cd") "B7A"))
//@pbe (constraint (= (f764f "hello world" "404" "hello world") "B13A"))
//@pbe (constraint (= (f764f "mno pqr st" "ab cd" "vvvvv") "B7A"))