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

function f345f(x_0)
{
	return lastLetter(len(x_0));
}

function f72f(x_0, x_1)
{
	return lastLetter(x_0);
}

function f639f(x_0, x_1, x_2)
{
	return beforeAfter(f72f(x_2, x_2));
}

function f105f(x_0, x_1, x_2)
{
	return concat(concat(x_2, x_0), lastLetter(x_1));
}

function f505f(x_0)
{
	return lastLetter(firstWord(x_0));
}

function f174f(x_0, x_1, x_2)
{
	return f105f(f72f(x_0, x_2), beforeAfter(x_2), x_1);
}

//@pbe (constraint (= (f690f "vvvvv") "5v"))
//@pbe (constraint (= (f690f "xyz") "3z"))
//@pbe (constraint (= (f690f "asdf") "4f"))