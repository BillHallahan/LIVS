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

function f443f(x_0, x_1, x_2)
{
	return firstWord(beforeAfter(x_1));
}

function f626f(x_0)
{
	return len(firstWord(x_0));
}

//@pbe (constraint (= (f791f "xyz" "ab cd") "BA"))
//@pbe (constraint (= (f791f "vvvvv" "hello world") "BA"))
//@pbe (constraint (= (f791f "hello world" "mno pqr st") "BhelloA"))
//@pbe (constraint (= (f791f "mno pqr st" "asdf") "BmnoA"))