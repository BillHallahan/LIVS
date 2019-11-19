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

function f430f(x_0, x_1)
{
	return beforeAfter(len(x_1));
}

function f680f(x_0)
{
	return len(f430f(x_0, x_0));
}

function f143f(x_0)
{
	return lastLetter(x_0);
}

function f71f(x_0, x_1)
{
	return beforeAfter(firstWord(x_1));
}

function f8f(x_0, x_1, x_2)
{
	return rep(len(x_0), x_1, f680f(x_2));
}

//@pbe (constraint (= (f204f "hello world") "BhelloA"))
//@pbe (constraint (= (f204f "xyz") "BA"))
//@pbe (constraint (= (f204f "404") "BA"))
//@pbe (constraint (= (f204f "404") "BA"))