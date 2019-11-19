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

function f753f(x_0)
{
	return firstWord(beforeAfter(x_0));
}

function f227f(x_0, x_1, x_2)
{
	return beforeAfter(firstWord(x_0));
}

function f280f(x_0)
{
	return rep(f753f(x_0), beforeAfter(x_0), len(x_0));
}

function f328f(x_0, x_1)
{
	return f753f(concat(x_0, x_0));
}

//@pbe (constraint (= (f362f "xyz" "") "BBAA"))
//@pbe (constraint (= (f362f "hello world" "404") "BBAA"))
//@pbe (constraint (= (f362f "asdf" "ab cd") "BBabAA"))