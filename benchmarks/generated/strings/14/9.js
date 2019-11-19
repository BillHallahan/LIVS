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

function f581f(x_0, x_1)
{
	return firstWord(concat(x_1, x_0));
}

function f444f(x_0, x_1)
{
	return lastLetter(f581f(x_0, x_0));
}

function f219f(x_0, x_1, x_2)
{
	return rep(f444f(x_1, x_2), x_0, len(x_2));
}

function f925f(x_0)
{
	return rep(f219f(x_0, x_0, x_0), rep(x_0, x_0, x_0), len(x_0));
}

function f72f(x_0, x_1, x_2)
{
	return concat(f925f(x_1), len(x_1));
}

function f17f(x_0)
{
	return concat(concat(x_0, x_0), beforeAfter(x_0));
}

function f579f(x_0, x_1)
{
	return beforeAfter(firstWord(x_1));
}

function f620f(x_0)
{
	return len(f581f(x_0, x_0));
}

function f696f(x_0)
{
	return f581f(x_0, f925f(x_0));
}

//@pbe (constraint (= (f451f "vvvvv" "xyz" "") "00"))
//@pbe (constraint (= (f451f "hello world" "hello world" "hello world") "o"))
//@pbe (constraint (= (f451f "mno pqr st" "vvvvv" "asdf") ""))