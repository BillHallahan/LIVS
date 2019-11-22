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

function f352f(x_0, x_1)
{
	return rep(f0f(x_0), x_1, concat(x_0, x_0));
}

function f247f(x_0)
{
	return f0f(x_0);
}

function f55f(x_0, x_1, x_2)
{
	return firstWord(x_0);
}

function f900f(x_0, x_1, x_2)
{
	return rep(f247f(x_2), x_1, concat(x_2, x_2));
}

function f676f(x_0, x_1, x_2)
{
	return f247f(rep(x_2, x_1, x_1));
}

function f898f(x_0, x_1)
{
	return f247f(concat(x_0, x_1));
}

//@pbe (constraint (= (f492f "asdf" "vvvvv") "1"))
//@pbe (constraint (= (f492f "404" "asdf") "1"))
//@pbe (constraint (= (f492f "mno pqr st" "xyz") "1"))