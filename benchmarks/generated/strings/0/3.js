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

//@pbe (constraint (= (f55f "vvvvv" "mno pqr st" "vvvvv") ""))
//@pbe (constraint (= (f55f "404" "xyz" "mno pqr st") ""))
//@pbe (constraint (= (f55f "asdf" "404" "ab cd") ""))
//@pbe (constraint (= (f55f "asdf" "ab cd" "hello world") ""))
//@pbe (constraint (= (f55f "asdf" "asdf" "404") ""))