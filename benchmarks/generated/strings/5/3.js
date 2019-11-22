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

function f342f(x_0, x_1, x_2)
{
	return len(x_1);
}

function f304f(x_0)
{
	return f342f(rep(x_0, x_0, x_0), beforeAfter(x_0), len(x_0));
}

function f802f(x_0)
{
	return lastLetter(x_0);
}

//@pbe (constraint (= (f424f "xyz" "mno pqr st") "B3A"))
//@pbe (constraint (= (f424f "ab cd" "vvvvv") "B5A"))
//@pbe (constraint (= (f424f "404" "vvvvv") "B3A"))
//@pbe (constraint (= (f424f "ab cd" "ab cd") "B5A"))
//@pbe (constraint (= (f424f "hello world" "mno pqr st") "B11A"))