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

function f308f(x_0, x_1, x_2)
{
	return lastLetter(len(x_1));
}

function f228f(x_0, x_1)
{
	return lastLetter(firstWord(x_1));
}

function f240f(x_0)
{
	return lastLetter(len(x_0));
}

function f772f(x_0)
{
	return concat(lastLetter(x_0), concat(x_0, x_0));
}

function f534f(x_0, x_1, x_2)
{
	return beforeAfter(f772f(x_1));
}

function f928f(x_0, x_1, x_2)
{
	return beforeAfter(x_1);
}

function f974f(x_0, x_1, x_2)
{
	return beforeAfter(firstWord(x_2));
}

function f817f(x_0, x_1, x_2)
{
	return len(lastLetter(x_0));
}

function f895f(x_0, x_1, x_2)
{
	return f308f(f240f(x_0), len(x_0), beforeAfter(x_1));
}

//@pbe (constraint (= (f709f "vvvvv") "vvvvv5"))
//@pbe (constraint (= (f709f "asdf") "asdf4"))
//@pbe (constraint (= (f709f "404") "4043"))
//@pbe (constraint (= (f709f "mno pqr st") "mno pqr st10"))