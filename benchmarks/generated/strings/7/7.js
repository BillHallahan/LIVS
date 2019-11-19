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

function f350f(x_0)
{
	return concat(x_0, concat(x_0, x_0));
}

function f967f(x_0, x_1)
{
	return concat(f350f(x_1), len(x_1));
}

function f611f(x_0, x_1, x_2)
{
	return len(f350f(x_2));
}

function f966f(x_0)
{
	return len(lastLetter(x_0));
}

function f808f(x_0)
{
	return beforeAfter(firstWord(x_0));
}

function f584f(x_0)
{
	return beforeAfter(f808f(x_0));
}

function f547f(x_0)
{
	return beforeAfter(f611f(x_0, x_0, x_0));
}

//@pbe (constraint (= (f468f "hello world" "ab cd" "mno pqr st") "15"))
//@pbe (constraint (= (f468f "404" "404" "") "0"))