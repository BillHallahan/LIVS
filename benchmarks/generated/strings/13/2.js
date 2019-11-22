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

function f741f(x_0, x_1, x_2)
{
	return lastLetter(len(x_1));
}

function f933f(x_0, x_1, x_2)
{
	return f741f(len(x_1), x_0, firstWord(x_2));
}

//@pbe (constraint (= (f449f "hello world" "404") "33"))
//@pbe (constraint (= (f449f "vvvvv" "404") "33"))
//@pbe (constraint (= (f449f "xyz" "hello world") "11"))
//@pbe (constraint (= (f449f "hello world" "mno pqr st") "00"))
//@pbe (constraint (= (f449f "hello world" "vvvvv") "55"))